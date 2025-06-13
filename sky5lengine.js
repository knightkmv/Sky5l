// ===================== ENGINE CORE =====================


// Enhanced constants and configuration
const ENGINE_CONFIG = {
  MAX_DEPTH: 128,
  TT_SIZE_MB: 256, // Larger transposition table
  LMR_BASE: 0.68,  // Tuned LMR parameters
  LMR_DIVISOR: 2.1,
  NULL_MOVE_R: 3,  // Null-move reduction
  PROBCUT_MARGINS: [40, 80, 120], // Depth-based margins
  ASPIRATION_WINDOW: 25, // Initial aspiration window
  CONTEMPT_FACTOR: 0.8  // Contempt scaling
};

const PHASE_VALUES = {
  PAWN: 0,
  KNIGHT: 1,
  BISHOP: 1,
  ROOK: 2,
  QUEEN: 4,
  KING: 0
};

// Tuned piece values (middlegame, endgame)
const PIECE_VALUES = [
  [0, 0],       // None
  [108, 135],   // Pawn (tuned)
  [328, 365],   // Knight
  [342, 385],   // Bishop
  [540, 600],   // Rook
  [1010, 1070], // Queen
  [20000, 20000] // King
];

class SKY5LChess {
    constructor() {
        // Enhanced Constants with better organization
        this.PIECE_TYPES = {
            PAWN: 1, KNIGHT: 2, BISHOP: 3, ROOK: 4, QUEEN: 5, KING: 6
        };
        
        this.COLORS = { WHITE: 0, BLACK: 1 };
        
        this.MOVE_FLAGS = {
            NORMAL: 0, CAPTURE: 1, PROMOTION: 2, 
            ENPASSANT: 3, CASTLING: 4, NULL: 5
        };
        
        // Evaluation constants
        this.INFINITY = 1000000;
        this.MATE_VALUE = 32000;
        this.MATE_SCORE = this.MATE_VALUE - 1000;
        this.TB_WIN = this.MATE_VALUE - 100;
        this.TB_LOSS = -this.TB_WIN;
        this.TB_DRAW = 0;
        
        this.PIECE_VALUES = PIECE_VALUES;

        // Game state
        this.bitboards = new BigUint64Array(12);
        this.occupancy = new BigUint64Array(3);
        this.side = this.COLORS.WHITE;
        this.castling = 0b1111;
        this.epSquare = -1;
        this.halfmoveClock = 0;
        this.fullmoveNumber = 1;
        this.hash = 0n;
        this.ply = 0;
        this.stack = [];
        this.gamePhase = 0;
        this.contempt = 0;
        this.rating = 4000;

        // Search parameters
        this.maxDepth = ENGINE_CONFIG.MAX_DEPTH;
        this.killers = Array.from({length: 2}, () => new Array(this.maxDepth).fill(null));
        this.historyHeuristic = new Int32Array(12 * 64 * 12 * 64); // 32-bit for better precision
        this.butterfly = new Int32Array(64 * 64);
        this.initTranspositionTable(ENGINE_CONFIG.TT_SIZE_MB);
        this.nodes = 0;
        this.startTime = 0;
        this.stopSearch = false;
        this.seldepth = 0;
        this.workers = [];
        this.searching = false;
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.pvTable = new Array(this.maxDepth).fill().map(() => new Array(this.maxDepth).fill(null));
        
        // Evaluation components
        this.evaluator = new EnhancedEvaluation(this);
        this.pawnCache = new PawnStructureCache();
        this.pst = this.initPST();
        this.initAttackTables();
        this.initEvaluationMasks();
        
        // Search enhancements
        this.searchExtensions = new AdvancedSearchExtensions(this);
        this.moveOrdering = new EnhancedMoveOrdering(this);
        this.timeManager = new EnhancedTimeManager();
        this.predCutting = new PredictiveCutting();
        this.parallelSearch = new ParallelSearch(this);
        this.lmrTable = this.initLMRTable();
        
        // Tablebases and opening book
        this.syzygy = new SyzygyTablebases();
        this.openingBook = new LearningBook();

        // Initialize components
        this.initMagicBitboards();
        this.initZobrist();
        this.initPieceSquareTables();
        this.setPosition("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    }

    async init() {
        await Promise.all([
            this.evaluator.init(),
            this.syzygy.init(),
            this.parallelSearch.init(),
            this.openingBook.load('book.bin')
        ]);
    }

    initTranspositionTable(sizeMB = 128) {
        const sizeEntries = Math.floor((sizeMB * 1024 * 1024) / 24);
        this.transpositionTable = new Array(sizeEntries);
        this.ttMask = sizeEntries - 1;
        this.ttGeneration = 0;
    }

    storeTT(depth, score, flag, move, isCutNode = false) {
        const index = Number(this.hash & BigInt(this.ttMask));
        const entry = this.transpositionTable[index] || {};

        if (isCutNode || !entry.depth || depth + 2 > entry.depth || this.ttGeneration !== entry.gen) {
            this.transpositionTable[index] = {
                key: this.hash,
                depth,
                score,
                flag,
                move,
                gen: this.ttGeneration,
                staticEval: this.evaluate()
            };
        }
    }

    probeTT() {
        const index = Number(this.hash & BigInt(this.ttMask));
        const entry = this.transpositionTable[index];
        
        if (entry && entry.key === this.hash) {
            const nextHash = this.hash ^ 1n;
            const nextIndex = Number(nextHash & BigInt(this.ttMask));
            this.transpositionTable[nextIndex]?.key;
            
            return {
                move: entry.move,
                score: entry.score,
                depth: entry.depth,
                flag: entry.flag,
                staticEval: entry.staticEval
            };
        }
        return null;
    }

    initLMRTable() {
        const table = new Array(64).fill().map(() => new Array(64).fill(0));
        for (let depth = 1; depth < 64; depth++) {
            for (let moves = 1; moves < 64; moves++) {
                table[depth][moves] = 0.75 + Math.log(depth) * Math.log(moves) / 2.3;
            }
        }
        return table;
    }

    initMagicBitboards() {
        this.bishopMagics = [
            0x89a1121896040240n, 0x2004844802002010n, 0x2068080051921000n, 0x62880a0220200808n,
            0x4042004000000n, 0x100822020200011n, 0xc00444222012000an, 0x28808801216001n,
            0x400492088408100n, 0x201c401040c0084n, 0x840800910a0010n, 0x82080240060n,
            0x2000840504006000n, 0x30010c4108405004n, 0x1008005410080802n, 0x8144042209100900n,
            0x208081020014400n, 0x4800201208ca00n, 0xf18140408012008n, 0x1004001202104000n,
            0x25200010900a000cn, 0x1008020010080400n, 0x2010080400080200n, 0x1010040200040800n,
            0x200808008004000n, 0x200844004000800n, 0x2100400400080200n, 0x2200040000801c00n,
            0x1480040000800800n, 0x4200040080800400n, 0x1200200040802000n, 0x2000400080801000n,
            0x4000800080801000n, 0x4000800080800800n, 0x8000800080800400n, 0x8001000080800400n,
            0x1000100008040200n, 0x2000100008040100n, 0x4000100008040080n, 0x8000100008040040n,
            0x1000010000804004n, 0x2000010000804002n, 0x4000010000804001n, 0x8000010000804000n,
            0x4800201208ca00n, 0x8144042209100900n, 0x1008020010080400n, 0x2010080400080200n,
            0x1010040200040800n, 0x200808008004000n, 0x200844004000800n, 0x2100400400080200n,
            0x2200040000801c00n, 0x1480040000800800n, 0x4200040080800400n, 0x1200200040802000n,
            0x2000400080801000n, 0x4000800080801000n, 0x4000800080800800n, 0x8000800080800400n,
            0x8001000080800400n, 0x1000100008040200n, 0x2000100008040100n, 0x4000100008040080n
        ];
        
        this.rookMagics = [
            0x80280013ff84ffffn, 0x5ffbfefdfef67fffn, 0xffeffaffeffd0bffn, 0x7fffff7fffbf0fffn,
            0x8038008013ff00ffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn,
            0xfffeffdfffff7fffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn,
            0xfffeffdfffff7fffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn,
            0xfffeffdfffff7fffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn,
            0xfffeffdfffff7fffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn,
            0xfffeffdfffff7fffn, 0x5ff7f7f7f7f7f7ffn, 0xfffdfefffffff7ffn, 0x7fffff7fffbf0fffn
        ];
        
        this.bishopAttacks = new Array(64).fill().map(() => new Array(512).fill(0n));
        this.rookAttacks = new Array(64).fill().map(() => new Array(4096).fill(0n));
        
        this.initSliderAttacks(true);  // Bishops
        this.initSliderAttacks(false); // Rooks
    }

    initSliderAttacks(isBishop) {
        for (let square = 0; square < 64; square++) {
            const mask = isBishop ? 
                this.getBishopMask(square) : this.getRookMask(square);
            const magic = isBishop ? 
                this.bishopMagics[square] : this.rookMagics[square];
            const shift = isBishop ? 55 : 52;
            
            let subset = 0n;
            do {
                const index = Number((subset * magic) >> BigInt(shift));
                const attacks = this.calculateSliderAttacks(square, subset, isBishop);
                
                if (isBishop) {
                    this.bishopAttacks[square][index] = attacks;
                } else {
                    this.rookAttacks[square][index] = attacks;
                }
                
                subset = (subset - mask) & mask;
            } while (subset !== 0n);
        }
    }

    getBishopMask(square) {
        let mask = 0n;
        const rank = Math.floor(square / 8);
        const file = square % 8;
        
        for (let r = rank + 1, f = file + 1; r < 7 && f < 7; r++, f++) {
            mask |= 1n << BigInt(r * 8 + f);
        }
        for (let r = rank + 1, f = file - 1; r < 7 && f > 0; r++, f--) {
            mask |= 1n << BigInt(r * 8 + f);
        }
        for (let r = rank - 1, f = file + 1; r > 0 && f < 7; r--, f++) {
            mask |= 1n << BigInt(r * 8 + f);
        }
        for (let r = rank - 1, f = file - 1; r > 0 && f > 0; r--, f--) {
            mask |= 1n << BigInt(r * 8 + f);
        }
        
        return mask;
    }

    getRookMask(square) {
        let mask = 0n;
        const rank = Math.floor(square / 8);
        const file = square % 8;
        
        for (let r = rank + 1; r < 7; r++) {
            mask |= 1n << BigInt(r * 8 + file);
        }
        for (let r = rank - 1; r > 0; r--) {
            mask |= 1n << BigInt(r * 8 + file);
        }
        for (let f = file + 1; f < 7; f++) {
            mask |= 1n << BigInt(rank * 8 + f);
        }
        for (let f = file - 1; f > 0; f--) {
            mask |= 1n << BigInt(rank * 8 + f);
        }
        
        return mask;
    }

    calculateSliderAttacks(square, subset, isBishop) {
        let attacks = 0n;
        const rank = Math.floor(square / 8);
        const file = square % 8;
        
        if (isBishop) {
            // Diagonal attacks
            for (let r = rank + 1, f = file + 1; r < 8 && f < 8; r++, f++) {
                const bit = 1n << BigInt(r * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let r = rank + 1, f = file - 1; r < 8 && f >= 0; r++, f--) {
                const bit = 1n << BigInt(r * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let r = rank - 1, f = file + 1; r >= 0 && f < 8; r--, f++) {
                const bit = 1n << BigInt(r * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let r = rank - 1, f = file - 1; r >= 0 && f >= 0; r--, f--) {
                const bit = 1n << BigInt(r * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
        } else {
            // Straight attacks
            for (let r = rank + 1; r < 8; r++) {
                const bit = 1n << BigInt(r * 8 + file);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let r = rank - 1; r >= 0; r--) {
                const bit = 1n << BigInt(r * 8 + file);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let f = file + 1; f < 8; f++) {
                const bit = 1n << BigInt(rank * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
            for (let f = file - 1; f >= 0; f--) {
                const bit = 1n << BigInt(rank * 8 + f);
                attacks |= bit;
                if (subset & bit) break;
            }
        }
        
        return attacks;
    }

    initAttackTables() {
        this.knightAttacks = new Array(64).fill(0n);
        this.kingAttacks = new Array(64).fill(0n);
        this.pawnAttacks = Array.from({length: 2}, () => new Array(64).fill(0n));

        for (let square = 0; square < 64; square++) {
            // Knight attacks
            const knightDeltas = [15, 17, 10, -6, -15, -17, -10, 6];
            for (const delta of knightDeltas) {
                const to = square + delta;
                if (to >= 0 && to < 64 && Math.abs((to % 8) - (square % 8)) <= 2) {
                    this.knightAttacks[square] |= 1n << BigInt(to);
                }
            }

            // King attacks
            const kingDeltas = [9, 8, 7, 1, -1, -7, -8, -9];
            for (const delta of kingDeltas) {
                const to = square + delta;
                if (to >= 0 && to < 64 && Math.abs((to % 8) - (square % 8)) <= 1) {
                    this.kingAttacks[square] |= 1n << BigInt(to);
                }
            }

            // Pawn attacks
            if (square > 7) { // White pawns
                if (square % 8 > 0) this.pawnAttacks[this.WHITE][square] |= 1n << BigInt(square - 9);
                if (square % 8 < 7) this.pawnAttacks[this.WHITE][square] |= 1n << BigInt(square - 7);
            }
            if (square < 56) { // Black pawns
                if (square % 8 > 0) this.pawnAttacks[this.BLACK][square] |= 1n << BigInt(square + 7);
                if (square % 8 < 7) this.pawnAttacks[this.BLACK][square] |= 1n << BigInt(square + 9);
            }
        }
    }

    initZobrist() {
        this.zobrist = {
            pieces: Array.from({length: 12}, () => new Array(64)),
            side: 0n,
            castling: new Array(16).fill(0n),
            ep: new Array(64).fill(0n)
        };

        const rand64 = () => {
            const buf = new Uint32Array(2);
            crypto.getRandomValues(buf);
            return (BigInt(buf[0]) << 32n) | BigInt(buf[1]);
        };

        for (let i = 0; i < 12; i++) {
            for (let j = 0; j < 64; j++) {
                this.zobrist.pieces[i][j] = rand64();
            }
        }
        this.zobrist.side = rand64();
        for (let i = 0; i < 16; i++) this.zobrist.castling[i] = rand64();
        for (let i = 0; i < 64; i++) this.zobrist.ep[i] = rand64();
    }

    initPieceSquareTables() {
        // Optimized Piece-Square Tables
        const tables = {
            pawn: [
                0,   0,   0,   0,   0,   0,   0,   0,
                98, 134,  61,  95,  68, 126,  34, -11,
                -6,   7,  26,  31,  65,  56,  25, -20,
                -14,  13,   6,  21,  23,  12,  17, -23,
                -27,  -2,  -5,  12,  17,   6,  10, -25,
                -26,  -4,  -4, -10,   3,   3,  33, -12,
                -35,  -1, -20, -23, -15,  24,  38, -22,
                0,   0,   0,   0,   0,   0,   0,   0
            ],
            knight: [
                -167, -89, -34, -49,  61, -97, -15, -107,
                -73, -41,  72,  36,  23,  62,   7,  -17,
                -47,  60,  37,  65,  84, 129,  73,   44,
                -9,  17,  19,  53,  37,  69,  18,   22,
                -13,   4,  16,  13,  28,  19,  21,   -8,
                -23,  -9,  12,  10,  19,  17,  25,  -16,
                -29, -53, -12,  -3,  -1,  18, -14,  -19,
                -105, -21, -58, -33, -17, -28, -19,  -23
            ],
            bishop: [
                -29,   4, -82, -37, -25, -42,   7,  -8,
                -26,  16, -18, -13,  30,  59,  18, -47,
                -16,  37,  43,  40,  35,  50,  37,  -2,
                -4,   5,  19,  50,  37,  37,   7,  -2,
                -6,  13,  13,  26,  34,  12,  10,   4,
                0,  15,  15,  15,  14,  27,  18,  10,
                4,  15,  16,   0,   7,  21,  33,   1,
                -33,  -3, -14, -21, -13, -12, -39, -21
            ],
            rook: [
                32,  42,  32,  51,  63,  9,  31,  43,
                27,  32,  58,  62,  80,  67,  26,  44,
                -5,  19,  26,  36,  17,  45,  61,  16,
                -24, -11,   7,  26,  24,  35,  -8, -20,
                -36, -26, -12,  -1,   9,  -7,   6, -23,
                -45, -25, -16, -17,   3,   0,  -5, -33,
                -44, -16, -20,  -9,  -1,  11,  -6, -71,
                -19, -13,   1,  17,  16,   7, -37, -26
            ],
            queen: [
                -28,   0,  29,  12,  59,  44,  43,  45,
                -24, -39,  -5,   1, -16,  57,  28,  54,
                -13, -17,   7,   8,  29,  56,  47,  57,
                -27, -27, -16, -16,  -1,  17,  -2,   1,
                -9, -26,  -9, -10,  -2,  -4,   3,  -3,
                -14,   2, -11,  -2,  -5,   2,  14,   5,
                -35,  -8,  11,   2,   8,  15,  -3,   1,
                -1, -18,  -9,  10, -15, -25, -31, -50
            ],
            king: [
                -65,  23,  16, -15, -56, -34,   2,  13,
                29,  -1, -20,  -7,  -8,  -4, -38, -29,
                -9,  24,   2, -16, -20,   6,  22, -22,
                -17, -20, -12, -27, -30, -25, -14, -36,
                -49,  -1, -27, -39, -46, -44, -33, -51,
                -14, -14, -22, -46, -44, -30, -15, -27,
                1,   7,  -8, -64, -43, -16,   9,   8,
                -15,  36,  12, -54,   8, -28,  24,  14
            ],
            kingEnd: [
                -74, -35, -18, -18, -11,  15,   4, -17,
                -12,  17,  14,  17,  17,  38,  23,  11,
                10,  17,  23,  15,  20,  45,  44,  13,
                -8,  22,  24,  27,  26,  33,  26,   3,
                -18,  -4,  21,  24,  27,  23,   9, -11,
                -19,  -3,  11,  21,  23,  16,   7,  -9,
                -27, -11,   4,  13,  14,   4,  -5, -17,
                -53, -34, -21, -11, -28, -14, -24, -43
            ]
        };

        this.pst = Array.from({length: 12}, () => new Array(64).fill(0));
        
        for (let i = 0; i < 64; i++) {
            // White pieces
            this.pst[this.WHITE * 6 + this.PAWN - 1][i] = tables.pawn[i];
            this.pst[this.WHITE * 6 + this.KNIGHT - 1][i] = tables.knight[i];
            this.pst[this.WHITE * 6 + this.BISHOP - 1][i] = tables.bishop[i];
            this.pst[this.WHITE * 6 + this.ROOK - 1][i] = tables.rook[i];
            this.pst[this.WHITE * 6 + this.QUEEN - 1][i] = tables.queen[i];
            this.pst[this.WHITE * 6 + this.KING - 1][i] = tables.king[i];
            
            // Black pieces (mirrored vertically)
            this.pst[this.BLACK * 6 + this.PAWN - 1][63 - i] = -tables.pawn[i];
            this.pst[this.BLACK * 6 + this.KNIGHT - 1][63 - i] = -tables.knight[i];
            this.pst[this.BLACK * 6 + this.BISHOP - 1][63 - i] = -tables.bishop[i];
            this.pst[this.BLACK * 6 + this.ROOK - 1][63 - i] = -tables.rook[i];
            this.pst[this.BLACK * 6 + this.QUEEN - 1][63 - i] = -tables.queen[i];
            this.pst[this.BLACK * 6 + this.KING - 1][63 - i] = -tables.king[i];
        }
    }

    initEvaluationMasks() {
        // File masks
        for (let file = 0; file < 8; file++) {
            this.fileMasks[file] = 0x0101010101010101n << BigInt(file);
        }

        // Passed pawn masks
        for (let sq = 0; sq < 64; sq++) {
            const file = sq % 8;
            const rank = Math.floor(sq / 8);
            
            // White passed pawn mask (opponent's pawns that can block/attack)
            let whiteMask = 0n;
            if (file > 0) {
                for (let r = rank + 1; r < 8; r++) {
                    whiteMask |= 1n << BigInt(r * 8 + file - 1);
                }
            }
            if (file < 7) {
                for (let r = rank + 1; r < 8; r++) {
                    whiteMask |= 1n << BigInt(r * 8 + file + 1);
                }
            }
            this.passedPawnMasks[this.BLACK][sq] = whiteMask;
            
            // Black passed pawn mask
            let blackMask = 0n;
            if (file > 0) {
                for (let r = rank - 1; r >= 0; r--) {
                    blackMask |= 1n << BigInt(r * 8 + file - 1);
                }
            }
            if (file < 7) {
                for (let r = rank - 1; r >= 0; r--) {
                    blackMask |= 1n << BigInt(r * 8 + file + 1);
                }
            }
            this.passedPawnMasks[this.WHITE][sq] = blackMask;
        }

        // Isolated pawn masks
        for (let file = 0; file < 8; file++) {
            let mask = 0n;
            if (file > 0) {
                for (let rank = 0; rank < 8; rank++) {
                    mask |= 1n << BigInt(rank * 8 + file - 1);
                }
            }
            if (file < 7) {
                for (let rank = 0; rank < 8; rank++) {
                    mask |= 1n << BigInt(rank * 8 + file + 1);
                }
            }
            this.isolatedMask[file] = mask;
        }

        // King safety masks and storm squares
        for (let sq = 0; sq < 64; sq++) {
            let mask = 0n;
            const file = sq % 8;
            const rank = Math.floor(sq / 8);
            
            const minFile = Math.max(0, file - 2);
            const maxFile = Math.min(7, file + 2);
            const minRank = Math.max(0, rank - 2);
            const maxRank = Math.min(7, rank + 2);
            
            for (let f = minFile; f <= maxFile; f++) {
                for (let r = minRank; r <= maxRank; r++) {
                    mask |= 1n << BigInt(r * 8 + f);
                    
                    // Storm squares are the 3 squares in front of the king
                    if ((this.side === this.WHITE && r > rank) || 
                        (this.side === this.BLACK && r < rank)) {
                        this.stormSquares[r * 8 + f] = 1;
                    }
                }
            }
            this.kingSafetyMask[sq] = mask;
        }

        // Mobility area (center squares)
        const centerFiles = [2, 3, 4, 5];
        const centerRanks = [2, 3, 4, 5];
        for (const file of centerFiles) {
            for (const rank of centerRanks) {
                this.mobilityArea[this.WHITE] |= 1n << BigInt(rank * 8 + file);
                this.mobilityArea[this.BLACK] |= 1n << BigInt((7 - rank) * 8 + file);
            }
        }
    }

    // ===================== MOVE GENERATION =====================
    generateMoves() {
        const moves = [];
        const us = this.side;
        const them = us ^ 1;
        const ourPieces = this.occupancy[us];
        const theirPieces = this.occupancy[them];
        const allPieces = this.occupancy[2];
        const inCheck = this.isInCheck();

        // Generate pawn moves
        const pawns = this.bitboards[us * 6 + this.PAWN - 1];
        let pawnBB = pawns;
        while (pawnBB) {
            const from = this.bitScanForward(pawnBB);
            pawnBB &= pawnBB - 1n;

            // Single push
            const push1 = from + (us === this.WHITE ? 8 : -8);
            if (!(allPieces & (1n << BigInt(push1)))) {
                // Promotion
                if ((us === this.WHITE && push1 >= 56) || (us === this.BLACK && push1 < 8)) {
                    for (let p = this.KNIGHT; p <= this.QUEEN; p++) {
                        moves.push(this.createMove(from, push1, this.PAWN, 0, this.FLAGS.PROMOTION, p));
                    }
                } else {
                    moves.push(this.createMove(from, push1, this.PAWN, 0, this.FLAGS.NORMAL));

                    // Double push
                    const rank = Math.floor(from / 8);
                    const push2 = from + (us === this.WHITE ? 16 : -16);
                    if ((us === this.WHITE && rank === 1) || (us === this.BLACK && rank === 6)) {
                        if (!(allPieces & (1n << BigInt(push2)))) {
                            moves.push(this.createMove(from, push2, this.PAWN, 0, this.FLAGS.NORMAL));
                        }
                    }
                }
            }

            // Captures
            const attacks = this.pawnAttacks[us][from];
            let captureBB = attacks & theirPieces;
            while (captureBB) {
                const to = this.bitScanForward(captureBB);
                captureBB &= captureBB - 1n;

                // Capture promotions
                if ((us === this.WHITE && to >= 56) || (us === this.BLACK && to < 8)) {
                    for (let p = this.KNIGHT; p <= this.QUEEN; p++) {
                        const captured = this.getPieceAt(to, them);
                        moves.push(this.createMove(from, to, this.PAWN, captured, this.FLAGS.PROMOTION, p));
                    }
                } else {
                    const captured = this.getPieceAt(to, them);
                    moves.push(this.createMove(from, to, this.PAWN, captured, this.FLAGS.CAPTURE));
                }
            }

            // En passant
            if (this.epSquare >= 0 && (attacks & (1n << BigInt(this.epSquare)))) {
                moves.push(this.createMove(from, this.epSquare, this.PAWN, this.PAWN, this.FLAGS.ENPASSANT));
            }
        }

        // Generate knight moves
        const knights = this.bitboards[us * 6 + this.KNIGHT - 1];
        let knightBB = knights;
        while (knightBB) {
            const from = this.bitScanForward(knightBB);
            knightBB &= knightBB - 1n;

            let attacks = this.knightAttacks[from] & ~ourPieces;
            while (attacks) {
                const to = this.bitScanForward(attacks);
                attacks &= attacks - 1n;
                const captured = this.getPieceAt(to, them);
                moves.push(this.createMove(from, to, this.KNIGHT, captured, 
                    captured ? this.FLAGS.CAPTURE : this.FLAGS.NORMAL));
            }
        }

        // Generate bishop moves
        const bishops = this.bitboards[us * 6 + this.BISHOP - 1];
        let bishopBB = bishops;
        while (bishopBB) {
            const from = this.bitScanForward(bishopBB);
            bishopBB &= bishopBB - 1n;

            let attacks = this.getBishopAttacks(from, allPieces) & ~ourPieces;
            while (attacks) {
                const to = this.bitScanForward(attacks);
                attacks &= attacks - 1n;
                const captured = this.getPieceAt(to, them);
                moves.push(this.createMove(from, to, this.BISHOP, captured, 
                    captured ? this.FLAGS.CAPTURE : this.FLAGS.NORMAL));
            }
        }

        // Generate rook moves
        const rooks = this.bitboards[us * 6 + this.ROOK - 1];
        let rookBB = rooks;
        while (rookBB) {
            const from = this.bitScanForward(rookBB);
            rookBB &= rookBB - 1n;

            let attacks = this.getRookAttacks(from, allPieces) & ~ourPieces;
            while (attacks) {
                const to = this.bitScanForward(attacks);
                attacks &= attacks - 1n;
                const captured = this.getPieceAt(to, them);
                moves.push(this.createMove(from, to, this.ROOK, captured, 
                    captured ? this.FLAGS.CAPTURE : this.FLAGS.NORMAL));
            }
        }

        // Generate queen moves
        const queens = this.bitboards[us * 6 + this.QUEEN - 1];
        let queenBB = queens;
        while (queenBB) {
            const from = this.bitScanForward(queenBB);
            queenBB &= queenBB - 1n;

            let attacks = (this.getBishopAttacks(from, allPieces) | 
                         this.getRookAttacks(from, allPieces)) & ~ourPieces;
            while (attacks) {
                const to = this.bitScanForward(attacks);
                attacks &= attacks - 1n;
                const captured = this.getPieceAt(to, them);
                moves.push(this.createMove(from, to, this.QUEEN, captured, 
                    captured ? this.FLAGS.CAPTURE : this.FLAGS.NORMAL));
            }
        }

        // Generate king moves
        const kings = this.bitboards[us * 6 + this.KING - 1];
        let kingBB = kings;
        while (kingBB) {
            const from = this.bitScanForward(kingBB);
            kingBB &= kingBB - 1n;

            let attacks = this.kingAttacks[from] & ~ourPieces;
            while (attacks) {
                const to = this.bitScanForward(attacks);
                attacks &= attacks - 1n;
                const captured = this.getPieceAt(to, them);
                moves.push(this.createMove(from, to, this.KING, captured, 
                    captured ? this.FLAGS.CAPTURE : this.FLAGS.NORMAL));
            }
        }

        // Generate castling moves
        if (!inCheck) {
            // Kingside
            if (this.canCastle(us, true)) {
                moves.push(this.createCastleMove(us, true));
            }
            // Queenside
            if (this.canCastle(us, false)) {
                moves.push(this.createCastleMove(us, false));
            }
        }

        return this.filterIllegalMoves(moves);
    }

    createMove(from, to, piece, captured, flags, promotion = 0) {
        return {
            from, to, piece, captured, flags, promotion,
            score: 0
        };
    }

    createCastleMove(us, kingside) {
        const rank = us === this.WHITE ? 0 : 7;
        const from = rank * 8 + 4;
        const to = rank * 8 + (kingside ? 6 : 2);
        return {
            from, to, piece: this.KING, captured: 0,
            flags: this.FLAGS.CASTLING,
            score: 0
        };
    }

    getBishopAttacks(square, occupancy) {
        const mask = this.getBishopMask(square);
        const magic = this.bishopMagics[square];
        const index = Number(((occupancy & mask) * magic) >> 55n);
        return this.bishopAttacks[square][index];
    }

    getRookAttacks(square, occupancy) {
        const mask = this.getRookMask(square);
        const magic = this.rookMagics[square];
        const index = Number(((occupancy & mask) * magic) >> 52n);
        return this.rookAttacks[square][index];
    }

    getQueenAttacks(square, occupancy) {
        return this.getBishopAttacks(square, occupancy) | this.getRookAttacks(square, occupancy);
    }

    isInCheck() {
        const kingSquare = this.bitScanForward(this.bitboards[this.side * 6 + this.KING - 1]);
        return this.isSquareAttacked(kingSquare, this.side ^ 1);
    }

    isSquareAttacked(square, bySide) {
        if (this.pawnAttacks[bySide ^ 1][square] & this.bitboards[bySide * 6 + this.PAWN - 1]) {
            return true;
        }

        if (this.knightAttacks[square] & this.bitboards[bySide * 6 + this.KNIGHT - 1]) {
            return true;
        }

        const bishopQueens = this.bitboards[bySide * 6 + this.BISHOP - 1] | 
                           this.bitboards[bySide * 6 + this.QUEEN - 1];
        if (this.getBishopAttacks(square, this.occupancy[2]) & bishopQueens) {
            return true;
        }

        const rookQueens = this.bitboards[bySide * 6 + this.ROOK - 1] | 
                         this.bitboards[bySide * 6 + this.QUEEN - 1];
        if (this.getRookAttacks(square, this.occupancy[2]) & rookQueens) {
            return true;
        }

        if (this.kingAttacks[square] & this.bitboards[bySide * 6 + this.KING - 1]) {
            return true;
        }

        return false;
    }

    canCastle(us, kingside) {
        if (!(this.castling & (us === this.WHITE ? (kingside ? 1 : 2) : (kingside ? 4 : 8)))) {
            return false;
        }

        const rank = us === this.WHITE ? 0 : 7;
        const kingFrom = rank * 8 + 4;
        const kingTo = rank * 8 + (kingside ? 6 : 2);
        const rookFrom = rank * 8 + (kingside ? 7 : 0);
        const rookTo = rank * 8 + (kingside ? 5 : 3);

        // Check if squares between king and rook are empty
        const betweenMask = kingside ? 0x60n : 0xEn;
        const betweenSquares = betweenMask << BigInt(rank * 8);
        if (this.occupancy[2] & betweenSquares) {
            return false;
        }

        // Check if king is not in check and doesn't move through attacked squares
        for (let sq = Math.min(kingFrom, kingTo); sq <= Math.max(kingFrom, kingTo); sq++) {
            if (this.isSquareAttacked(sq, us ^ 1)) {
                return false;
            }
        }

        return true;
    }

    filterIllegalMoves(moves) {
        const legalMoves = [];
        const us = this.side;
        
        for (const move of moves) {
            const undo = this.makeMove(move);
            const kingSquare = this.bitScanForward(this.bitboards[us * 6 + this.KING - 1]);
            const inCheck = this.isSquareAttacked(kingSquare, us ^ 1);
            this.undoMove(move, undo);
            
            if (!inCheck) {
                legalMoves.push(move);
            }
        }
        
        return legalMoves;
    }

    getPieceAt(square, color) {
        const mask = 1n << BigInt(square);
        for (let piece = this.PAWN; piece <= this.KING; piece++) {
            if (this.bitboards[color * 6 + piece - 1] & mask) {
                return piece;
            }
        }
        return 0;
    }

    // ===================== MOVE MAKING =====================
    makeMove(move) {
        const undo = {
            hash: this.hash,
            castling: this.castling,
            epSquare: this.epSquare,
            halfmoveClock: this.halfmoveClock,
            captured: move.captured,
            capturedSquare: -1,
            piece: move.piece
        };

        const us = this.side;
        const them = us ^ 1;
        const fromBB = 1n << BigInt(move.from);
        const toBB = 1n << BigInt(move.to);

        // Update hash for moving piece
        this.hash ^= this.zobrist.pieces[us * 6 + move.piece - 1][move.from];
        this.hash ^= this.zobrist.pieces[us * 6 + move.piece - 1][move.to];

        // Handle captures
        if (move.flags === this.FLAGS.CAPTURE || move.flags === this.FLAGS.ENPASSANT) {
            let capturedSquare = move.to;
            if (move.flags === this.FLAGS.ENPASSANT) {
                capturedSquare = move.to + (us === this.WHITE ? -8 : 8);
            }
            
            const capturedPiece = move.flags === this.FLAGS.ENPASSANT ? this.PAWN : move.captured;
            const capturedBB = 1n << BigInt(capturedSquare);
            
            // Remove captured piece
            this.bitboards[them * 6 + capturedPiece - 1] &= ~capturedBB;
            this.occupancy[them] &= ~capturedBB;
            this.occupancy[2] &= ~capturedBB;
            
            // Update hash
            this.hash ^= this.zobrist.pieces[them * 6 + capturedPiece - 1][capturedSquare];
            
            undo.capturedSquare = capturedSquare;
        }

        // Move the piece
        this.bitboards[us * 6 + move.piece - 1] ^= fromBB | toBB;
        this.occupancy[us] ^= fromBB | toBB;
        this.occupancy[2] ^= fromBB | toBB;

        // Handle promotions
        if (move.flags === this.FLAGS.PROMOTION) {
            // Remove pawn
            this.bitboards[us * 6 + this.PAWN - 1] &= ~toBB;
            this.hash ^= this.zobrist.pieces[us * 6 + this.PAWN - 1][move.to];
            
            // Add promoted piece
            this.bitboards[us * 6 + move.promotion - 1] |= toBB;
            this.hash ^= this.zobrist.pieces[us * 6 + move.promotion - 1][move.to];
        }

        // Handle castling
        if (move.flags === this.FLAGS.CASTLING) {
            const rank = us === this.WHITE ? 0 : 7;
            const rookFrom = rank * 8 + (move.to > move.from ? 7 : 0);
            const rookTo = rank * 8 + (move.to > move.from ? 5 : 3);
            const rookBB = (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
            
            this.bitboards[us * 6 + this.ROOK - 1] ^= rookBB;
            this.occupancy[us] ^= rookBB;
            this.occupancy[2] ^= rookBB;
            
            // Update hash
            this.hash ^= this.zobrist.pieces[us * 6 + this.ROOK - 1][rookFrom];
            this.hash ^= this.zobrist.pieces[us * 6 + this.ROOK - 1][rookTo];
        }

        // Update castling rights
        const castlingBefore = this.castling;
        this.castling &= ~((fromBB | toBB) & 0x91n ? 0b0011 : 0);
        this.castling &= ~((fromBB | toBB) & 0x9100000000000000n ? 0b1100 : 0);
        if (this.castling !== castlingBefore) {
            this.hash ^= this.zobrist.castling[castlingBefore];
            this.hash ^= this.zobrist.castling[this.castling];
        }

        // Update en passant square
        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
        }
        this.epSquare = -1;
        
        if (move.piece === this.PAWN && Math.abs(move.to - move.from) === 16) {
            this.epSquare = move.from + (us === this.WHITE ? 8 : -8);
            this.hash ^= this.zobrist.ep[this.epSquare];
        }

        // Update halfmove clock
        if (move.piece === this.PAWN || move.flags === this.FLAGS.CAPTURE) {
            this.halfmoveClock = 0;
        } else {
            this.halfmoveClock++;
        }

        // Update fullmove number
        if (this.side === this.BLACK) {
            this.fullmoveNumber++;
        }

        // Switch side
        this.side = them;
        this.hash ^= this.zobrist.side;

        this.ply++;
        this.stack.push(undo);

        return undo;
    }

    undoMove(move, undo) {
        this.ply--;
        this.stack.pop();
        
        const us = this.side ^ 1;
        const them = this.side;
        const fromBB = 1n << BigInt(move.from);
        const toBB = 1n << BigInt(move.to);

        // Switch side first
        this.side = us;
        this.hash ^= this.zobrist.side;

        // Restore castling rights
        if (this.castling !== undo.castling) {
            this.hash ^= this.zobrist.castling[this.castling];
            this.castling = undo.castling;
            this.hash ^= this.zobrist.castling[undo.castling];
        }

        // Restore en passant square
        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
        }
        this.epSquare = undo.epSquare;
        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
        }

        // Restore halfmove clock and fullmove number
        this.halfmoveClock = undo.halfmoveClock;
        if (this.side === this.BLACK) {
            this.fullmoveNumber--;
        }

        // Handle promotions
        if (move.flags === this.FLAGS.PROMOTION) {
            // Remove promoted piece
            this.bitboards[us * 6 + move.promotion - 1] &= ~toBB;
            this.hash ^= this.zobrist.pieces[us * 6 + move.promotion - 1][move.to];
            
            // Add back pawn
            this.bitboards[us * 6 + this.PAWN - 1] |= fromBB;
            this.hash ^= this.zobrist.pieces[us * 6 + this.PAWN - 1][move.from];
        } else {
            // Move piece back
            this.bitboards[us * 6 + move.piece - 1] ^= fromBB | toBB;
            this.hash ^= this.zobrist.pieces[us * 6 + move.piece - 1][move.from];
            this.hash ^= this.zobrist.pieces[us * 6 + move.piece - 1][move.to];
        }

        // Update occupancies
        this.occupancy[us] ^= fromBB | toBB;
        this.occupancy[2] ^= fromBB | toBB;

        // Handle castling
        if (move.flags === this.FLAGS.CASTLING) {
            const rank = us === this.WHITE ? 0 : 7;
            const rookFrom = rank * 8 + (move.to > move.from ? 7 : 0);
            const rookTo = rank * 8 + (move.to > move.from ? 5 : 3);
            const rookBB = (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
            
            this.bitboards[us * 6 + this.ROOK - 1] ^= rookBB;
            this.occupancy[us] ^= rookBB;
            this.occupancy[2] ^= rookBB;
            
            // Update hash
            this.hash ^= this.zobrist.pieces[us * 6 + this.ROOK - 1][rookFrom];
            this.hash ^= this.zobrist.pieces[us * 6 + this.ROOK - 1][rookTo];
        }

        // Handle captures
        if (move.flags === this.FLAGS.CAPTURE || move.flags === this.FLAGS.ENPASSANT) {
            const capturedSquare = undo.capturedSquare;
            const capturedBB = 1n << BigInt(capturedSquare);
            const capturedPiece = move.flags === this.FLAGS.ENPASSANT ? this.PAWN : move.captured;
            
            // Restore captured piece
            this.bitboards[them * 6 + capturedPiece - 1] |= capturedBB;
            this.occupancy[them] |= capturedBB;
            this.occupancy[2] |= capturedBB;
            
            // Update hash
            this.hash ^= this.zobrist.pieces[them * 6 + capturedPiece - 1][capturedSquare];
        }

        // Restore hash
        this.hash = undo.hash;
    }

    makeNullMove() {
        const undo = {
            hash: this.hash,
            epSquare: this.epSquare
        };

        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
            this.epSquare = -1;
        }

        this.side ^= 1;
        this.hash ^= this.zobrist.side;

        this.ply++;
        this.stack.push(undo);

        return undo;
    }

    undoNullMove(undo) {
        this.ply--;
        this.stack.pop();

        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
        }
        this.epSquare = undo.epSquare;
        if (this.epSquare !== -1) {
            this.hash ^= this.zobrist.ep[this.epSquare];
        }

        this.side ^= 1;
        this.hash ^= this.zobrist.side;

        this.hash = undo.hash;
    }
    // ===================== SEARCH =====================
    
    async search(depth, alpha, beta, cutNode = false, isMainThread = true) {
        if (this.stopSearch) return alpha;
        if (this.halfmoveClock >= 100 || this.isRepetition()) 
            return this.getDynamicContempt();

        // TT probe with improved replacement strategy
        const tt = this.probeTT();
        const ttMove = tt?.move || null;
        const ttScore = tt?.score || -this.INFINITY;
        
        if (tt && tt.depth >= depth) {
            if (tt.flag === 0) return ttScore;
            if (tt.flag === 1 && ttScore >= beta) return beta;
            if (tt.flag === 2 && ttScore <= alpha) return alpha;
        }

        // Check extension with more aggressive conditions
        const inCheck = this.isInCheck();
        const extension = this.searchExtensions.shouldExtend(depth, ttMove, this);
        depth += extension;

        // QSearch with improved stand-pat pruning
        if (depth <= 0) {
            const standPat = this.evaluate();
            if (standPat >= beta) return beta;
            alpha = Math.max(alpha, standPat);
            return this.qSearch(alpha, beta);
        }

        // Null move pruning with verification search
        if (!inCheck && depth >= 3 && this.hasNonPawns()) {
            const R = ENGINE_CONFIG.NULL_MOVE_R + Math.min(2, depth / 6);
            this.makeNullMove();
            const nullScore = -await this.search(depth - R, -beta, -beta + 1, true);
            this.undoNullMove();
            
            if (nullScore >= beta) {
                if (depth >= 8) { // Verification search
                    const verifyScore = await this.search(depth - R - 2, beta - 50, beta, false);
                    if (verifyScore >= beta) return beta;
                } else {
                    return beta;
                }
            }
        }

        // ProbCut with tuned margins
        if (depth >= 4 && !cutNode && Math.abs(alpha - beta) === 1) {
            const probCutScore = await this.predCutting.probCut(depth, beta, this);
            if (probCutScore >= beta) return beta;
        }

        // Aspiration window with dynamic sizing
        let window = ENGINE_CONFIG.ASPIRATION_WINDOW + Math.min(50, depth * 4);
        if (depth >= 5 && alpha > -this.MATE_SCORE && beta < this.MATE_SCORE) {
            const score = await this.search(depth-1, alpha, beta, cutNode, isMainThread);
            alpha = Math.max(alpha, score - window);
            beta = Math.min(beta, score + window);
        }
        
        const moves = this.generateMoves();
        if (moves.length === 0) {
            return inCheck ? -this.MATE_VALUE + this.ply : this.getDynamicContempt();
        }
        
        this.moveOrdering.orderMoves(moves, ttMove, depth, this);

        let bestScore = -this.INFINITY;
        let bestMove = moves[0];
        let legalMoves = 0;
        const improving = !inCheck && this.evaluate() > 
            (this.stack.length >= 2 ? this.stack[this.stack.length - 2].staticEval : -this.INFINITY);

        for (let i = 0; i < moves.length; i++) {
            const move = moves[i];
            
            // Advanced pruning conditions
            if (this.searchExtensions.shouldPrune(move, depth, improving)) {
                continue;
            }
            
            // Enhanced LMR with more accurate reduction formula
            let reduction = 0;
            if (depth >= 3 && legalMoves > 2 + depth / 4 && !inCheck && 
                !move.captured && !move.promotion && !this.isThreatening(move)) {
                reduction = Math.floor(
                    ENGINE_CONFIG.LMR_BASE + 
                    Math.log(depth) * Math.log(legalMoves) / ENGINE_CONFIG.LMR_DIVISOR
                );
                if (!improving) reduction++;
                if (cutNode) reduction++;
                reduction = Math.min(depth - 1, Math.max(0, reduction));
                
                // Increase reduction for moves with bad history
                const history = this.historyHeuristic[
                    this.side * 49152 + move.from * 768 + move.piece * 64 + move.to];
                if (history < 0) reduction += Math.min(2, -history / 20000);
            }
            
            const undo = this.makeMove(move);
            let score;
            
            if (reduction > 0) {
                score = -await this.search(depth - 1 - reduction, -beta, -alpha, true, false);
                if (score > alpha) {
                    score = -await this.search(depth - 1, -beta, -alpha, false, false);
                }
            } else {
                score = -await this.search(depth - 1, -beta, -alpha, false, false);
            }
            
            this.undoMove(move, undo);
            
            if (score >= beta) {
                this.moveOrdering.updateHistory(move, depth, beta - alpha, this);
                
                if (!move.captured && !move.promotion) {
                    this.killers[1][this.ply] = this.killers[0][this.ply];
                    this.killers[0][this.ply] = move;
                }
                
                this.storeTT(depth, beta, 1, move, true);
                return beta;
            }
            
            if (score > bestScore) {
                bestScore = score;
                bestMove = move;
                if (score > alpha) {
                    alpha = score;
                }
            }
            
            legalMoves++;
        }
        
        this.storeTT(depth, bestScore, bestScore > alpha ? 0 : 2, bestMove);
        return bestScore;
    }
    qSearch(alpha, beta) {
        const standPat = this.evaluate();
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        const phase = this.gamePhase() / 256;
        const deltaMargin = 75 + 150 * phase;
        if (standPat + deltaMargin < alpha) {
            return alpha;
        }

        const moves = this.generateMoves().filter(move => {
            if (move.flags === this.FLAGS.PROMOTION) {
                return move.promotion === this.QUEEN || this.see(move, -50);
            }
            return (move.flags === this.FLAGS.CAPTURE) && 
                   this.see(move, -25 - Math.abs(standPat - alpha));
        });

        moves.sort((a, b) => {
            const aValue = (a.captured ? this.pieceValue(a.captured) * 10 : 0) - 
                          this.pieceValue(a.piece) + 
                          (this.see(a, 0) ? 500 : 0);
            const bValue = (b.captured ? this.pieceValue(b.captured) * 10 : 0) - 
                          this.pieceValue(b.piece) + 
                          (this.see(b, 0) ? 500 : 0);
            
            const aCheck = this.givesCheck(a);
            const bCheck = this.givesCheck(b);
            if (aCheck !== bCheck) return aCheck ? -1 : 1;
            
            return bValue - aValue;
        });

        for (const move of moves) {
            const undo = this.makeMove(move);
            const score = -this.qSearch(-beta, -alpha);
            this.undoMove(move, undo);

            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }

        if (alpha === standPat && this.hasHangingPieces()) {
            return this.qSearch(alpha, beta);
        }

        return alpha;
    }

    givesCheck(move) {
        const undo = this.makeMove(move);
        const inCheck = this.isInCheck();
        this.undoMove(move, undo);
        return inCheck;
    }

    hasHangingPieces() {
        const us = this.side;
        const them = us ^ 1;
        let hanging = 0n;

        for (let piece = this.PAWN; piece <= this.QUEEN; piece++) {
            let bb = this.bitboards[them * 6 + piece - 1];
            while (bb) {
                const sq = this.bitScanForward(bb);
                bb &= bb - 1n;
                if (!this.see({ from: sq, to: sq, piece, captured: 0 }, -1)) {
                    hanging |= 1n << BigInt(sq);
                }
            }
        }
        return hanging !== 0n;
    }

    see(move, threshold = 0) {
        const from = move.from;
        const to = move.to;
        const us = this.side;
        const them = us ^ 1;
        
        if (move.flags === this.FLAGS.PROMOTION && move.promotion === this.QUEEN) 
            return true;
        if (this.pieceValue(move.piece) < this.pieceValue(move.captured)) 
            return true;

        let balance = this.pieceValue(move.captured) - threshold;
        balance -= this.pieceValue(move.piece);
        if (balance >= 0) return true;
        
        let occupied = this.occupancy[2];
        let attackers = this.getAttackers(to, occupied, us, them);
        occupied ^= 1n << BigInt(from);
        
        if ((attackers & this.occupancy[them]) === 0n) 
            return true;
        
        const gains = [this.pieceValue(move.captured)];
        let side = them;
        let depth = 0;
        
        while (true) {
            const lva = this.getLeastValuableAttacker(attackers & this.occupancy[side], occupied);
            if (!lva.piece) break;
            
            gains.push(this.pieceValue(lva.piece));
            if (depth > 0) {
                balance = -balance - gains[depth];
                if (balance >= 0) break;
            }
            
            occupied ^= 1n << BigInt(lva.square);
            attackers |= this.getXrayAttackers(to, occupied, us, them);
            side ^= 1;
            depth++;
        }
        
        while (--depth >= 0) {
            gains[depth] = Math.max(0, gains[depth] - gains[depth + 1]);
        }
        
        return (balance + gains[0]) >= 0;
    }

    getAttackers(square, occupied, us, them) {
        return (
            (this.pawnAttacks[us][square] & this.bitboards[them * 6 + this.PAWN - 1]) |
            (this.knightAttacks[square] & this.bitboards[them * 6 + this.KNIGHT - 1]) |
            (this.getBishopAttacks(square, occupied) & (this.bitboards[them * 6 + this.BISHOP - 1] | 
                                                     this.bitboards[them * 6 + this.QUEEN - 1])) |
            (this.getRookAttacks(square, occupied) & (this.bitboards[them * 6 + this.ROOK - 1] | 
                                                   this.bitboards[them * 6 + this.QUEEN - 1])) |
            (this.kingAttacks[square] & this.bitboards[them * 6 + this.KING - 1])
        );
    }

    getXrayAttackers(square, occupied, us, them) {
        let xray = 0n;
        const bishopsQueens = this.bitboards[them * 6 + this.BISHOP - 1] | 
                            this.bitboards[them * 6 + this.QUEEN - 1];
        const rooksQueens = this.bitboards[them * 6 + this.ROOK - 1] | 
                           this.bitboards[them * 6 + this.QUEEN - 1];
        
        const bishopXray = this.getBishopAttacks(square, occupied) & bishopsQueens;
        const rookXray = this.getRookAttacks(square, occupied) & rooksQueens;
        
        return bishopXray | rookXray;
    }

    getLeastValuableAttacker(attackers, occupied) {
        const masks = [
            0xFFFFFFFFFFFFFFFFn,
            this.bitboards[this.PAWN - 1],
            this.bitboards[this.KNIGHT - 1],
            this.bitboards[this.BISHOP - 1],
            this.bitboards[this.ROOK - 1],
            this.bitboards[this.QUEEN - 1],
            this.bitboards[this.KING - 1]
        ];
        
        for (let piece = this.PAWN; piece <= this.KING; piece++) {
            const pieces = attackers & masks[piece];
            if (pieces) {
                const square = this.bitScanForward(pieces);
                return { piece, square };
            }
        }
        return { piece: 0, square: 0 };
    }

    pieceValue(piece) {
        return piece ? this.PIECE_VALUES[piece][0] : 0;
    }

    evaluate() {
        return this.evaluator.evaluate(this);
    }

    gamePhase() {
        let phase = 0;
        
        phase += this.popCount(this.bitboards[this.WHITE * 6 + this.KNIGHT - 1] | 
                 this.bitboards[this.BLACK * 6 + this.KNIGHT - 1]) * 1;
        
        phase += this.popCount(this.bitboards[this.WHITE * 6 + this.BISHOP - 1] | 
                 this.bitboards[this.BLACK * 6 + this.BISHOP - 1]) * 1;
        
        phase += this.popCount(this.bitboards[this.WHITE * 6 + this.ROOK - 1] | 
                 this.bitboards[this.BLACK * 6 + this.ROOK - 1]) * 2;
        
        phase += this.popCount(this.bitboards[this.WHITE * 6 + this.QUEEN - 1] | 
                 this.bitboards[this.BLACK * 6 + this.QUEEN - 1]) * 4;
        
        return Math.min(256, phase);
    }

    evaluateKingSafety() {
        const us = this.side;
        const them = us ^ 1;
        const kingSquare = this.bitScanForward(this.bitboards[us * 6 + this.KING - 1]);
        let safety = 0;
        
        const pawnShield = this.kingSafetyMask[kingSquare] & this.bitboards[us * 6 + this.PAWN - 1];
        safety += this.popCount(pawnShield) * 20;
        
        let storm = 0;
        let stormBB = this.kingSafetyMask[kingSquare] & this.stormSquares;
        while (stormBB) {
            const sq = this.bitScanForward(stormBB);
            stormBB &= stormBB - 1n;
            
            if (this.bitboards[them * 6 + this.PAWN - 1] & (1n << BigInt(sq))) {
                storm += 25;
            }
        }
        safety -= storm;
        
        const file = kingSquare % 8;
        if (!(this.bitboards[us * 6 + this.PAWN - 1] & this.fileMasks[file])) {
            safety -= 40;
            if ((this.bitboards[them * 6 + this.ROOK - 1] | this.bitboards[them * 6 + this.QUEEN - 1]) & this.fileMasks[file]) {
                safety -= 25;
            }
        }
        
        let attackers = 0;
        let attackWeight = 0;
        
        if (this.bitboards[them * 6 + this.QUEEN - 1]) {
            const queenAttacks = this.getQueenAttacks(kingSquare, this.occupancy[2]);
            if (queenAttacks & this.bitboards[them * 6 + this.QUEEN - 1]) {
                attackers++;
                attackWeight += 6;
            }
        }
        
        if (this.bitboards[them * 6 + this.ROOK - 1]) {
            const rookAttacks = this.getRookAttacks(kingSquare, this.occupancy[2]);
            if (rookAttacks & this.bitboards[them * 6 + this.ROOK - 1]) {
                attackers++;
                attackWeight += 4;
            }
        }
        
        if (this.bitboards[them * 6 + this.BISHOP - 1]) {
            const bishopAttacks = this.getBishopAttacks(kingSquare, this.occupancy[2]);
            if (bishopAttacks & this.bitboards[them * 6 + this.BISHOP - 1]) {
                attackers++;
                attackWeight += 3;
            }
        }
        
        if (this.bitboards[them * 6 + this.KNIGHT - 1]) {
            const knightAttacks = this.knightAttacks[kingSquare];
            if (knightAttacks & this.bitboards[them * 6 + this.KNIGHT - 1]) {
                attackers++;
                attackWeight += 3;
            }
        }
        
        if (this.bitboards[them * 6 + this.PAWN - 1]) {
            const pawnAttacks = this.pawnAttacks[us][kingSquare];
            if (pawnAttacks & this.bitboards[them * 6 + this.PAWN - 1]) {
                attackers++;
                attackWeight += 2;
            }
        }
        
        if (attackers > 0) {
            safety -= this.kingSafetyTable[Math.min(attackWeight, 99)] * (1 + attackers / 4);
        }
        
        return safety;
    }

    evaluateMobility() {
        const us = this.side;
        const them = us ^ 1;
        let mobility = 0;
        
        let knights = this.bitboards[us * 6 + this.KNIGHT - 1];
        while (knights) {
            const sq = this.bitScanForward(knights);
            knights &= knights - 1n;
            
            const attacks = this.knightAttacks[sq] & ~this.occupancy[us];
            mobility += this.popCount(attacks) * 3;
            
            if (attacks & this.mobilityArea[us]) {
                mobility += 2;
            }
        }
        
        let bishops = this.bitboards[us * 6 + this.BISHOP - 1];
        while (bishops) {
            const sq = this.bitScanForward(bishops);
            bishops &= bishops - 1n;
            
            const attacks = this.getBishopAttacks(sq, this.occupancy[2]) & ~this.occupancy[us];
            mobility += this.popCount(attacks) * 2;
            
            if ((attacks & 0x8142241818244281n) !== 0n) {
                mobility += 3;
            }
        }
        
        let rooks = this.bitboards[us * 6 + this.ROOK - 1];
        while (rooks) {
            const sq = this.bitScanForward(rooks);
            rooks &= rooks - 1n;
            
            const attacks = this.getRookAttacks(sq, this.occupancy[2]) & ~this.occupancy[us];
            mobility += this.popCount(attacks);
            
            const file = sq % 8;
            if (!(this.bitboards[us * 6 + this.PAWN - 1] & this.fileMasks[file])) {
                mobility += 3;
                if (!(this.bitboards[them * 6 + this.PAWN - 1] & this.fileMasks[file])) {
                    mobility += 5;
                }
            }
        }
        
        let queens = this.bitboards[us * 6 + this.QUEEN - 1];
        while (queens) {
            const sq = this.bitScanForward(queens);
            queens &= queens - 1n;
            
            const attacks = (this.getBishopAttacks(sq, this.occupancy[2]) | 
                           this.getRookAttacks(sq, this.occupancy[2])) & ~this.occupancy[us];
            mobility += this.popCount(attacks) * 1;
        }
        
        return mobility;
    }

    bitScanForward(bb) {
        if (bb === 0n) return -1;
        return 63 - Math.clz32(Number(bb & -bb));
    }

    popCount(bb) {
        let count = 0;
        while (bb) {
            count++;
            bb &= bb - 1n;
        }
        return count;
    }

    computeHash() {
        let hash = 0n;
        
        for (let piece = 0; piece < 12; piece++) {
            let bb = this.bitboards[piece];
            while (bb) {
                const sq = this.bitScanForward(bb);
                bb &= bb - 1n;
                hash ^= this.zobrist.pieces[piece][sq];
            }
        }
        
        if (this.side === this.WHITE) hash ^= this.zobrist.side;
        
        hash ^= this.zobrist.castling[this.castling];
        
        if (this.epSquare !== -1) hash ^= this.zobrist.ep[this.epSquare];
        
        return hash;
    }

    squareToIndex(square) {
        const file = square.charCodeAt(0) - 'a'.charCodeAt(0);
        const rank = 8 - parseInt(square[1]);
        return rank * 8 + file;
    }

    charToPiece(c) {
        switch (c.toLowerCase()) {
            case 'p': return (c === 'p' ? this.BLACK : this.WHITE) * 6 + this.PAWN;
            case 'n': return (c === 'n' ? this.BLACK : this.WHITE) * 6 + this.KNIGHT;
            case 'b': return (c === 'b' ? this.BLACK : this.WHITE) * 6 + this.BISHOP;
            case 'r': return (c === 'r' ? this.BLACK : this.WHITE) * 6 + this.ROOK;
            case 'q': return (c === 'q' ? this.BLACK : this.WHITE) * 6 + this.QUEEN;
            case 'k': return (c === 'k' ? this.BLACK : this.WHITE) * 6 + this.KING;
            default: return -1;
        }
    }

    getFEN() {
        let fen = '';
        
        for (let rank = 7; rank >= 0; rank--) {
            let empty = 0;
            for (let file = 0; file < 8; file++) {
                const square = rank * 8 + file;
                let piece = -1;
                
                for (let i = 0; i < 12; i++) {
                    if (this.bitboards[i] & (1n << BigInt(square))) {
                        piece = i;
                        break;
                    }
                }
                
                if (piece === -1) {
                    empty++;
                } else {
                    if (empty > 0) {
                        fen += empty;
                        empty = 0;
                    }
                    const pieceChar = this.pieceToChar(piece);
                    fen += pieceChar;
                }
            }
            
            if (empty > 0) fen += empty;
            if (rank > 0) fen += '/';
        }
        
        fen += this.side === this.WHITE ? ' w ' : ' b ';
        
        let castlingStr = '';
        if (this.castling & 0b0001) castlingStr += 'K';
        if (this.castling & 0b0010) castlingStr += 'Q';
        if (this.castling & 0b0100) castlingStr += 'k';
        if (this.castling & 0b1000) castlingStr += 'q';
        fen += castlingStr || '-';
        
        fen += ' ';
        if (this.epSquare !== -1) {
            const file = this.epSquare % 8;
            const rank = Math.floor(this.epSquare / 8);
            fen += String.fromCharCode('a'.charCodeAt(0) + file) + (rank + 1);
        } else {
            fen += '-';
        }
        
        fen += ' ' + this.halfmoveClock + ' ' + this.fullmoveNumber;
        
        return fen;
    }

    pieceToChar(pieceIndex) {
        const color = Math.floor(pieceIndex / 6);
        const piece = pieceIndex % 6 + 1;
        const chars = ['', 'P', 'N', 'B', 'R', 'Q', 'K'];
        return color === this.WHITE ? chars[piece].toUpperCase() : chars[piece].toLowerCase();
    }

    async getBestMove(options = {}) {
        this.startTime = Date.now();
        this.timeManager.init(
            options.time || 5000, 
            options.increment || 0, 
            options.movesToGo || 40, 
            this
        );
        
        this.nodes = 0;
        this.seldepth = 0;
        this.stopSearch = false;
        this.lastScore = 0;
        this.scoreDrops = 0;

        if (this.openingBook.ready) {
            const bookMove = this.openingBook.getMove(this.getFEN());
            if (bookMove) return bookMove;
        }

        if (this.syzygy.ready && this.popCount(this.occupancy[2]) <= this.syzygy.maxPieces) {
            const tbResult = this.syzygy.probe(this);
            if (tbResult) return tbResult.bestMove;
        }

        let bestMove = null;
        let bestScore = -this.INFINITY;
        
        for (let depth = 1; depth <= this.maxDepth; depth++) {
            const score = await this.search(depth, -this.INFINITY, this.INFINITY, false, true);

            const ttEntry = this.transpositionTable[this.hash % this.transpositionTable.length];
            if (ttEntry && ttEntry.key === this.hash) {
                bestMove = ttEntry.move;
                bestScore = ttEntry.score;
            }

            const elapsed = Date.now() - this.startTime;
            if (this.timeManager.shouldStop(elapsed, depth, bestScore, this.nodes)) {
                break;
            }

            if (Math.abs(score) >= this.MATE_SCORE) {
                break;
            }
        }

        return bestMove || this.generateMoves()[0];
    }

    setPosition(fen) {
        this.bitboards.fill(0n);
        this.occupancy.fill(0n);
        
        const parts = fen.split(' ');
        const piecePlacement = parts[0];
        const sideToMove = parts[1];
        const castlingRights = parts.length > 2 ? parts[2] : 'KQkq';
        const enPassant = parts.length > 3 ? parts[3] : '-';
        const halfmoveClock = parts.length > 4 ? parseInt(parts[4]) : 0;
        const fullmoveNumber = parts.length > 5 ? parseInt(parts[5]) : 1;
        
        let rank = 7;
        let file = 0;
        
        for (const c of piecePlacement) {
            if (c === '/') {
                rank--;
                file = 0;
            } else if (/\d/.test(c)) {
                file += parseInt(c);
            } else {
                const piece = this.charToPiece(c);
                if (piece !== -1) {
                    const square = rank * 8 + file;
                    this.bitboards[piece] |= 1n << BigInt(square);
                    this.occupancy[piece < 6 ? this.WHITE : this.BLACK] |= 1n << BigInt(square);
                    file++;
                }
            }
        }
        
        this.occupancy[2] = this.occupancy[0] | this.occupancy[1];
        
        this.side = sideToMove === 'w' ? this.WHITE : this.BLACK;
        
        this.castling = 0;
        if (castlingRights.includes('K')) this.castling |= 0b0001;
        if (castlingRights.includes('Q')) this.castling |= 0b0010;
        if (castlingRights.includes('k')) this.castling |= 0b0100;
        if (castlingRights.includes('q')) this.castling |= 0b1000;
        
        this.epSquare = enPassant === '-' ? -1 : this.squareToIndex(enPassant);
        
        this.halfmoveClock = halfmoveClock;
        this.fullmoveNumber = fullmoveNumber;
        
        this.hash = this.computeHash();
        
        this.stack = [];
        this.ply = 0;
    }

    isRepetition() {
        if (this.halfmoveClock < 4) return false;
        
        let count = 0;
        for (let i = this.stack.length - 2; i >= 0 && i >= this.stack.length - this.halfmoveClock; i -= 2) {
            if (this.stack[i].hash === this.hash) {
                count++;
                if (count >= 2) return true;
            }
        }
        return false;
    }

    hasNonPawns() {
        const us = this.side;
        return (this.bitboards[us * 6 + this.KNIGHT - 1] |
                this.bitboards[us * 6 + this.BISHOP - 1] |
                this.bitboards[us * 6 + this.ROOK - 1] |
                this.bitboards[us * 6 + this.QUEEN - 1]) !== 0n;
    }

    getDynamicContempt() {
        const phase = this.gamePhase() / 256;
        const ratingDiff = this.rating - 2500;
        const contemptFactor = 0.5 + phase * 0.3 + Math.min(1, ratingDiff / 500) * 0.2;
        return this.contempt * contemptFactor;
    }

    isThreatening(move) {
        const us = this.side;
        const them = us ^ 1;
        
        const undo = this.makeMove(move);
        const givesCheck = this.isInCheck();
        this.undoMove(move, undo);
        
        if (givesCheck) return true;
        
        const queenSquare = this.bitScanForward(this.bitboards[them * 6 + this.QUEEN - 1]);
        if (queenSquare >= 0) {
            const attacks = this.getAttackers(queenSquare, this.occupancy[2], them, us);
            if (attacks & (1n << BigInt(move.to))) {
                return true;
            }
        }
        
        const fromBB = 1n << BigInt(move.from);
        const toBB = 1n << BigInt(move.to);
        
        const rookQueens = this.bitboards[us * 6 + this.ROOK - 1] | 
                          this.bitboards[us * 6 + this.QUEEN - 1];
        if (rookQueens) {
            const file = move.from % 8;
            const rank = Math.floor(move.from / 8);
            
            const filePieces = this.occupancy[2] & this.fileMasks[file];
            if ((filePieces & rookQueens) && (filePieces & fromBB)) {
                return true;
            }
            
            const rankMask = 0xffn << BigInt(rank * 8);
            const rankPieces = this.occupancy[2] & rankMask;
            if ((rankPieces & rookQueens) && (rankPieces & fromBB)) {
                return true;
            }
        }
        
        const bishopQueens = this.bitboards[us * 6 + this.BISHOP - 1] | 
                           this.bitboards[us * 6 + this.QUEEN - 1];
        if (bishopQueens) {
            const attacks = this.getBishopAttacks(move.to, this.occupancy[2] ^ fromBB);
            if (attacks & bishopQueens) {
                return true;
            }
        }
        
        return false;
    }
}
// ===================== ENHANCED EVALUATION =====================
class EnhancedEvaluation {
    constructor(engine) {
        this.engine = engine;
        this.nnue = new EnhancedNNUE();
        this.ready = false;
        this.endgameKnowledge = new EndgameKnowledge();
    }

    async init() {
        try {
            await Promise.all([
                this.nnue.loadModel('nnue.bin'),
                this.endgameKnowledge.init()
            ]);
            this.ready = true;
        } catch (e) {
            console.error("Evaluation initialization failed:", e);
            this.ready = false;
        }
    }

    evaluate(position) {
        const phase = position.gamePhase() / 256;
        
        // NNUE evaluation (dominant in endgame)
        const nnueScore = this.nnue.ready ? this.nnue.evaluate(position) : 0;
        
        // Classical evaluation (strong in middlegame)
        let score = this.classicalEval(position, phase);
        
        // Specialized evaluation terms
        score += this.evalBishopPair(position, phase);
        score += this.evalRookOnOpenFile(position);
        score += this.evalKingTropism(position);
        score += this.evalPassedPawns(position, phase);
        score += this.endgameKnowledge.evaluate(position);
        
        // Dynamic weighting
        const nnueWeight = 0.2 + phase * 0.7; // NNUE stronger in endgame
        const classicalWeight = 1.5 - phase * 0.7; // Classical stronger in middlegame
        score = (nnueScore * nnueWeight + score * classicalWeight) / (nnueWeight + classicalWeight);
        
        // Tempo bonus and contempt
        const tempo = 12;
        const contempt = position.getDynamicContempt() * ENGINE_CONFIG.CONTEMPT_FACTOR;
        return position.side === position.COLORS.WHITE ? score + tempo + contempt : score - tempo - contempt;
    }
    classicalEval(position, phase) {
        let score = 0;
        
        score += this.evalMaterial(position, phase);
        score += this.evalPST(position, phase);
        score += position.pawnCache.evaluate(position) * (0.5 + phase * 0.5);
        score += position.evaluateMobility() * (1.0 - phase * 0.5);
        score += position.evaluateKingSafety() * (1.0 - phase * 0.7);
        score += this.evalSpace(position, phase);
        score += this.evalOutposts(position, phase);
        
        return score;
    }
    
    evalBishopPair(position, phase) {
        const whiteBishops = position.popCount(position.bitboards[position.WHITE * 6 + position.BISHOP - 1]);
        const blackBishops = position.popCount(position.bitboards[position.BLACK * 6 + position.BISHOP - 1]);
        
        let score = 0;
        if (whiteBishops >= 2) score += 30 * (1 - phase * 0.5);
        if (blackBishops >= 2) score -= 30 * (1 - phase * 0.5);
        
        return score;
    }

    evalRookOnOpenFile(position) {
        let score = 0;
        
        for (let file = 0; file < 8; file++) {
            const fileMask = position.fileMasks[file];
            const whitePawns = position.bitboards[position.WHITE * 6 + position.PAWN - 1] & fileMask;
            const blackPawns = position.bitboards[position.BLACK * 6 + position.PAWN - 1] & fileMask;
            
            const whiteRooks = position.bitboards[position.WHITE * 6 + position.ROOK - 1] & fileMask;
            if (whiteRooks) {
                if (!whitePawns) {
                    score += !blackPawns ? 25 : 15;
                }
            }
            
            const blackRooks = position.bitboards[position.BLACK * 6 + position.ROOK - 1] & fileMask;
            if (blackRooks) {
                if (!blackPawns) {
                    score -= !whitePawns ? 25 : 15;
                }
            }
        }
        
        return score;
    }

    evalKingTropism(position) {
        const whiteKing = position.bitScanForward(position.bitboards[position.WHITE * 6 + position.KING - 1]);
        const blackKing = position.bitScanForward(position.bitboards[position.BLACK * 6 + position.KING - 1]);
        
        if (whiteKing === -1 || blackKing === -1) return 0;
        
        const wkFile = whiteKing % 8;
        const wkRank = Math.floor(whiteKing / 8);
        const bkFile = blackKing % 8;
        const bkRank = Math.floor(blackKing / 8);
        
        const distance = Math.abs(wkFile - bkFile) + Math.abs(wkRank - bkRank);
        
        const phase = position.gamePhase() / 256;
        return phase > 0.7 ? (14 - distance) * 5 : 0;
    }

    evalPassedPawns(position, phase) {
        let score = 0;
        const us = position.side;
        const them = us ^ 1;
        
        let whitePawns = position.bitboards[position.WHITE * 6 + position.PAWN - 1];
        while (whitePawns) {
            const sq = position.bitScanForward(whitePawns);
            whitePawns &= whitePawns - 1n;
            
            if (!(position.bitboards[position.BLACK * 6 + position.PAWN - 1] & 
                position.passedPawnMasks[position.WHITE][sq])) {
                const file = sq % 8;
                const rank = Math.floor(sq / 8);
                
                let pawnValue = 30;
                const promotionDist = 7 - rank;
                pawnValue += (6 - promotionDist) * 20;
                
                if ((position.bitboards[position.WHITE * 6 + position.PAWN - 1] & 
                     position.pawnAttacks[position.BLACK][sq])) {
                    pawnValue += 20;
                }
                
                const behindMask = us === position.WHITE 
                    ? (0xffffffffffffffffn << BigInt(sq + 8))
                    : (0xffffffffffffffffn >> BigInt(64 - sq));
                
                if (position.bitboards[position.WHITE * 6 + position.ROOK - 1] & behindMask) {
                    pawnValue += 15;
                }
                
                const kingSq = position.bitScanForward(position.bitboards[position.WHITE * 6 + position.KING - 1]);
                if (kingSq >= 0) {
                    const kingDist = Math.max(Math.abs((kingSq % 8) - file), 
                                            Math.abs(Math.floor(kingSq / 8) - rank));
                    pawnValue += (7 - kingDist) * 5;
                }
                
                const enemyKingSq = position.bitScanForward(position.bitboards[position.BLACK * 6 + position.KING - 1]);
                if (enemyKingSq >= 0) {
                    const enemyKingDist = Math.max(Math.abs((enemyKingSq % 8) - file), 
                                                 Math.abs(Math.floor(enemyKingSq / 8) - rank));
                    pawnValue -= (7 - enemyKingDist) * 5;
                }
                
                score += pawnValue;
            }
        }
        
        let blackPawns = position.bitboards[position.BLACK * 6 + position.PAWN - 1];
        while (blackPawns) {
            const sq = position.bitScanForward(blackPawns);
            blackPawns &= blackPawns - 1n;
            
            if (!(position.bitboards[position.WHITE * 6 + position.PAWN - 1] & 
                position.passedPawnMasks[position.BLACK][sq])) {
                const file = sq % 8;
                const rank = Math.floor(sq / 8);
                
                let pawnValue = 30;
                const promotionDist = rank;
                pawnValue += (6 - promotionDist) * 20;
                
                if ((position.bitboards[position.BLACK * 6 + position.PAWN - 1] & 
                     position.pawnAttacks[position.WHITE][sq])) {
                    pawnValue += 20;
                }
                
                const behindMask = us === position.BLACK 
                    ? (0xffffffffffffffffn << BigInt(sq + 8))
                    : (0xffffffffffffffffn >> BigInt(64 - sq));
                
                if (position.bitboards[position.BLACK * 6 + position.ROOK - 1] & behindMask) {
                    pawnValue += 15;
                }
                
                const kingSq = position.bitScanForward(position.bitboards[position.BLACK * 6 + position.KING - 1]);
                if (kingSq >= 0) {
                    const kingDist = Math.max(Math.abs((kingSq % 8) - file), 
                                            Math.abs(Math.floor(kingSq / 8) - rank));
                    pawnValue += (7 - kingDist) * 5;
                }
                
                const enemyKingSq = position.bitScanForward(position.bitboards[position.WHITE * 6 + position.KING - 1]);
                if (enemyKingSq >= 0) {
                    const enemyKingDist = Math.max(Math.abs((enemyKingSq % 8) - file), 
                                                 Math.abs(Math.floor(enemyKingSq / 8) - rank));
                    pawnValue -= (7 - enemyKingDist) * 5;
                }
                
                score -= pawnValue;
            }
        }
        
        return score * (0.5 + phase * 0.5);
    }

    evalMaterial(position, phase) {
        let score = 0;
        
        for (let piece = position.PAWN; piece <= position.QUEEN; piece++) {
            const whiteCount = position.popCount(position.bitboards[position.WHITE * 6 + piece - 1]);
            score += whiteCount * 
                    (position.PIECE_VALUES[piece][0] * (1 - phase) + 
                     position.PIECE_VALUES[piece][1] * phase);
            
            const blackCount = position.popCount(position.bitboards[position.BLACK * 6 + piece - 1]);
            score -= blackCount * 
                    (position.PIECE_VALUES[piece][0] * (1 - phase) + 
                     position.PIECE_VALUES[piece][1] * phase);
        }
        
        return score;
    }

    evalPST(position, phase) {
        let score = 0;
        
        for (let piece = 0; piece < 6; piece++) {
            let bb = position.bitboards[position.WHITE * 6 + piece];
            while (bb) {
                const sq = position.bitScanForward(bb);
                bb &= bb - 1n;
                score += position.pst[position.WHITE * 6 + piece][sq];
            }
            
            bb = position.bitboards[position.BLACK * 6 + piece];
            while (bb) {
                const sq = position.bitScanForward(bb);
                bb &= bb - 1n;
                score -= position.pst[position.BLACK * 6 + piece][sq];
            }
        }
        
        const whiteKingSq = position.bitScanForward(position.bitboards[position.WHITE * 6 + position.KING - 1]);
        const blackKingSq = position.bitScanForward(position.bitboards[position.BLACK * 6 + position.KING - 1]);
        
        score += position.pst[position.WHITE * 6 + position.KING - 1][whiteKingSq] * (1 - phase);
        score -= position.pst[position.BLACK * 6 + position.KING - 1][blackKingSq] * (1 - phase);
        
        return score;
    }

    evalSpace(position, phase) {
        let space = 0;
        const us = position.side;
        const them = us ^ 1;
        
        const whiteSpace = position.popCount(position.occupancy[position.WHITE] & 0xffffffff00000000n);
        const blackSpace = position.popCount(position.occupancy[position.BLACK] & 0xffffffffn);
        
        space += (whiteSpace - blackSpace) * (us === position.WHITE ? 1 : -1) * 5;
        
        const center = 0x3c3c3c3c0000n;
        space += position.popCount(position.occupancy[us] & center) * 10;
        space -= position.popCount(position.occupancy[them] & center) * 10;
        
        return space * (1.0 - phase * 0.5);
    }

    evalOutposts(position, phase) {
        let outposts = 0;
        const us = position.side;
        const them = us ^ 1;
        
        let knights = position.bitboards[us * 6 + position.KNIGHT - 1];
        while (knights) {
            const sq = position.bitScanForward(knights);
            knights &= knights - 1n;
            
            const rank = Math.floor(sq / 8);
            const file = sq % 8;
            
            if (rank >= (us === position.WHITE ? 4 : 3)) {
                const pawnProtect = us === position.WHITE ? 
                    (position.pawnAttacks[position.BLACK][sq] & position.bitboards[us * 6 + position.PAWN - 1]) :
                    (position.pawnAttacks[position.WHITE][sq] & position.bitboards[us * 6 + position.PAWN - 1]);
                
                const enemyPawnAttack = position.pawnAttacks[us][sq] & 
                    position.bitboards[them * 6 + position.PAWN - 1];
                
                if (pawnProtect && !enemyPawnAttack) {
                    outposts += 20;
                    if (rank >= (us === position.WHITE ? 5 : 2)) outposts += 10;
                }
            }
        }
        
        return outposts * (1.0 - phase * 0.7);
    }
}
// ===================== COMPLETE NNUE IMPLEMENTATION =====================

class EnhancedNNUE {
    constructor() {
        this.featureTransformer = new NNUEFeatureTransformer();
        this.network = new NNUENetwork();
        this.cache = new NNUEBucketCache(1 << 20); // 1MB cache
        this.ready = false;
    }

    async loadModel(url) {
        try {
            // In a real implementation, load actual NNUE weights
            // This would typically be a binary file with quantized weights
            const response = await fetch(url);
            const buffer = await response.arrayBuffer();
            const data = new Int16Array(buffer);
            
            // Parse the weights (format depends on your NNUE implementation)
            this.featureTransformer.weights = data.subarray(0, 41024 * 256);
            this.network.weights = data.subarray(41024 * 256);
            
            this.ready = true;
        } catch (e) {
            console.error("NNUE loading failed:", e);
            this.ready = false;
        }
    }

    evaluate(position) {
        if (!this.ready) return 0;
        
        const key = position.hash & this.cache.mask;
        let accumulator = this.cache.get(key);
        
        if (!accumulator) {
            accumulator = this.featureTransformer.transform(position);
            this.cache.set(key, accumulator);
        }
        
        const output = this.network.propagate(accumulator);
        return output / 100.0; // Convert to centipawns
    }
}
class NNUEFeatureTransformer {
    constructor() {
        this.weights = new Int16Array(256 * 41024);
    }

    transform(position) {
        const features = [];
        
        for (let piece = 0; piece < 12; piece++) {
            let bb = position.bitboards[piece];
            while (bb) {
                const sq = position.bitScanForward(bb);
                bb &= bb - 1n;
                features.push(piece * 64 + sq);
            }
        }
        
        features.push(768 + this.evalPawnStructure(position));
        features.push(1024 + this.evalKingSafety(position));
        
        return features;
    }
    
    evalPawnStructure(position) {
        let hash = 0;
        for (let file = 0; file < 8; file++) {
            const whitePawns = position.popCount(position.bitboards[position.WHITE * 6 + position.PAWN - 1] & position.fileMasks[file]);
            const blackPawns = position.popCount(position.bitboards[position.BLACK * 6 + position.PAWN - 1] & position.fileMasks[file]);
            hash = (hash * 3 + whitePawns) * 3 + blackPawns;
        }
        return hash % 256;
    }
    
    evalKingSafety(position) {
        const us = position.side;
        const them = us ^ 1;
        const kingSquare = position.bitScanForward(position.bitboards[us * 6 + position.KING - 1]);
        
        let safety = 0;
        const pawnShield = position.kingSafetyMask[kingSquare] & position.bitboards[us * 6 + position.PAWN - 1];
        safety += position.popCount(pawnShield) * 2;
        
        const file = kingSquare % 8;
        if (!(position.bitboards[us * 6 + position.PAWN - 1] & position.fileMasks[file])) {
            safety -= 2;
        }
        
        return Math.min(255, Math.max(0, safety + 128));
    }
}

class NNUENetwork {
    constructor() {
        this.weights = new Int16Array(32 * 256);
    }

    propagate(features) {
        let output = 0;
        
        for (let i = 0; i < features.length; i++) {
            const feature = features[i];
            for (let j = 0; j < 32; j++) {
                output += this.weights[j * 256 + feature];
            }
        }
        
        return output;
    }
}

class NNUEBucketCache {
    constructor(size = 1 << 20) {
        this.size = size;
        this.mask = BigInt(size - 1);
        this.keys = new BigUint64Array(size);
        this.accumulators = new Array(size);
    }
    
    get(key) {
        const index = Number(key & this.mask);
        return this.keys[index] === key ? this.accumulators[index] : null;
    }
    
    set(key, value) {
        const index = Number(key & this.mask);
        this.keys[index] = key;
        this.accumulators[index] = value;
    }
}
// ===================== ADVANCED SEARCH EXTENSIONS =====================

class AdvancedSearchExtensions {
    constructor(engine) {
        this.engine = engine;
        this.threatTable = new Int16Array(64 * 64);
    }

    shouldExtend(depth, move, position) {
        let extension = 0;
        
        // Check extensions (more aggressive in deep searches)
        if (this.givesCheck(move, position)) {
            extension = 1 + (depth < 8 ? 1 : 0);
        }
        
        // Singular extension (from Stockfish)
        if (depth >= 8 && !extension && this.isSingular(position, move, depth)) {
            extension = 1;
        }
        
        // Pawn push near promotion
        if (move.piece === position.PIECE_TYPES.PAWN) {
            const rank = Math.floor(move.to / 8);
            if ((position.side === position.COLORS.WHITE && rank >= 4) || 
                (position.side === position.COLORS.BLACK && rank <= 3)) {
                extension = Math.max(extension, 1);
            }
        }
        
        // Recapture extensions
        if (position.stack.length > 0 && move.to === position.stack[position.stack.length-1].move.to) {
            extension = Math.max(extension, 1);
        }
        
        return extension;
    }

    shouldPrune(move, depth, improving) {
        // Futility pruning
        if (depth <= 7 && !improving && !move.captured && !move.promotion) {
            const margin = 150 + 175 * depth;
            if (this.engine.evaluate() + margin <= this.engine.alpha) {
                return true;
            }
        }
        
        // History pruning
        if (depth <= 4 && !move.captured && !move.promotion) {
            const history = this.engine.historyHeuristic[
                this.engine.side * 49152 + move.from * 768 + move.piece * 64 + move.to];
            if (history < depth * depth * 2) {
                return true;
            }
        }
        
        return false;
    } ...
}

// ===================== ENHANCED MOVE ORDERING =====================
class EnhancedMoveOrdering {
    constructor(engine) {
        this.engine = engine;
        this.historyMax = 20000;
        this.counterMoves = Array.from({length: 12}, () => new Array(64).fill(null));
        this.followupMoves = Array.from({length: 12}, () => new Array(64).fill(null));
    }

    orderMoves(moves, ttMove, depth, position) {
        const [prevMove, prevPrevMove] = this.getPreviousMoves(position);
        
        for (const move of moves) {
            let score = 0;
            
            // 1. TT move
            if (ttMove && this.isSameMove(move, ttMove)) {
                score = 1000000;
            }
            // 2. Winning captures
            else if (move.captured && this.engine.see(move, 0)) {
                score = 90000 + this.captureValue(move);
            }
            // 3. Killer moves
            else if (this.isKiller(move, position)) {
                score = 80000;
            }
            // 4. Counter moves
            else if (this.isCounterMove(move, prevMove)) {
                score = 70000;
            }
            // 5. Follow-up moves
            else if (this.isFollowup(move, prevPrevMove)) {
                score = 60000;
            }
            // 6. History heuristic
            else {
                score = this.getHistoryScore(move, position);
            }
            
            // 7. Promotion bonus
            if (move.flags === position.MOVE_FLAGS.PROMOTION) {
                score += 50000 + (move.promotion === position.PIECE_TYPES.QUEEN ? 200 : 100);
            }
            
            // 8. Check bonus
            if (this.givesCheck(move, position)) score += 30000;
            
            // 9. Passed pawn push in endgame
            if (move.piece === position.PIECE_TYPES.PAWN) {
                const phase = position.gamePhase() / 256;
                if (phase > 0.6) {
                    const rank = Math.floor(move.to / 8);
                    const promotionDist = position.side === position.COLORS.WHITE ? 7 - rank : rank;
                    score += (6 - promotionDist) * 20;
                }
            }
            
            move.score = score;
        }
        
        moves.sort((a, b) => b.score - a.score);
    }

    updateHistory(move, depth, bonus, position) {
        // History heuristic
        this.engine.historyHeuristic[position.side][move.from][move.piece][move.to] += 
            depth * depth * Math.min(10, bonus);
        
        // Butterfly heuristic
        this.engine.butterfly[move.from][move.to] += depth * depth;
        
        // Counter move heuristic
        if (position.stack.length > 0) {
            const prevMove = position.stack[position.stack.length - 1].move;
            if (prevMove) {
                this.counterMoves[prevMove.piece][prevMove.to] = move;
            }
        }
        
        // Follow-up move heuristic
        if (position.stack.length > 1) {
            const prevPrevMove = position.stack[position.stack.length - 2].move;
            if (prevPrevMove) {
                this.followupMoves[prevPrevMove.piece][prevPrevMove.to] = move;
            }
        }
        
        // Cap history values
        this.engine.historyHeuristic[position.side][move.from][move.piece][move.to] = 
            Math.min(this.historyMax, 
            Math.max(-this.historyMax, 
            this.engine.historyHeuristic[position.side][move.from][move.piece][move.to]));
    }
}
class EnhancedTimeManager {
    constructor() {
        this.timeBudget = 0;
        this.panicTime = 0;
        this.maxNodes = 0;
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.bestMoveChanges = 0;
    }

    init(timeLeft, increment, movesToGo, position) {
        const phase = position.gamePhase() / 256;
        const materialDiff = Math.abs(position.evaluator.evalMaterial(position, 0));
        const complexity = this.calculateComplexity(position);
        
        // Expected game length based on phase
        const expectedMoves = movesToGo || (30 - phase * 10);
        
        // Base time per move with increment
        let baseTime = timeLeft / expectedMoves + increment * 0.8;
        
        // Adjust for game phase (spend more time in complex middlegame)
        baseTime *= (1.3 - phase * 0.4);
        
        // Adjust for material imbalance (spend more time in sharp positions)
        baseTime *= (1.0 + Math.min(0.5, materialDiff / 800));
        
        // Adjust for position complexity
        baseTime *= (1.0 + complexity * 0.5);
        
        // Minimum time to avoid instant moves
        this.timeBudget = Math.max(50, Math.min(timeLeft * 0.95, baseTime));
        
        // Panic time is 20% of budget or 10% of remaining, whichever is smaller
        this.panicTime = Math.min(timeLeft * 0.1, this.timeBudget * 0.2);
        
        // Node limit based on time control
        this.maxNodes = timeLeft < 30000 ? 1e6 : 5e6;
        
        // Reset tracking variables
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.bestMoveChanges = 0;
    }

    calculateComplexity(position) {
        let complexity = 0;
        
        // Material imbalance
        const materialDiff = Math.abs(
            position.evaluator.evalMaterial(position, 0) - 
            position.evaluator.evalMaterial(position, 1)
        );
        complexity += Math.min(0.3, materialDiff / 500);
        
        // Pawn structure
        complexity += Math.min(0.4, Math.abs(position.pawnCache.evaluate(position)) / 200);
        
        // Mobility
        complexity += Math.min(0.3, Math.abs(position.evaluateMobility()) / 150);
        
        // King safety
        complexity += Math.min(0.4, Math.abs(position.evaluateKingSafety()) / 100);
        
        return Math.min(1, complexity);
    }

    shouldStop(elapsed, depth, score, nodes) {
        // Always finish current depth if we're in panic mode
        if (elapsed > this.panicTime && depth > 1) {
            return true;
        }
        
        // Node limit
        if (nodes >= this.maxNodes) return true;
        
        // Score drop detection
        if (score < this.lastScore - 100) {
            this.scoreDrops++;
            if (this.scoreDrops >= 2 && elapsed > this.timeBudget * 0.3) {
                return true;
            }
        }
        
        // Best move stability check
        if (depth >= 6 && Math.abs(score - this.lastScore) < 20) {
            this.bestMoveChanges++;
            if (this.bestMoveChanges >= 3 && elapsed > this.timeBudget * 0.5) {
                return true;
            }
        }
        
        this.lastScore = score;
        return elapsed >= this.timeBudget;
    }
}

class PredictiveCutting {
    constructor() {
        this.cutTable = new Int8Array(64 * 64 * 6); // [from][to][piece]
        this.history = new Int16Array(64 * 64);
        this.probCutMargin = [50, 75, 100]; // Depth-based margins
    }

    shouldCut(move, depth, beta) {
        const index = move.from * 64 + move.to;
        const pieceBonus = this.cutTable[index * 6 + move.piece];
        const historyBonus = this.history[index] / 100;
        
        const threshold = -50 + 
                         (depth * 10) + 
                         pieceBonus + 
                         historyBonus;
        
        return beta > threshold;
    }

    updateCutStats(move, depth, success) {
        const index = move.from * 64 + move.to;
        const delta = success ? depth * 2 : -depth;
        
        this.cutTable[index * 6 + move.piece] = 
            Math.max(-127, Math.min(127, 
                this.cutTable[index * 6 + move.piece] + delta));
        
        this.history[index] = 
            Math.max(-32767, Math.min(32767, 
                this.history[index] + delta * 10));
    }

    async probCut(depth, beta, position) {
        const probCutDepth = depth - 4;
        const probCutBeta = beta + this.probCutMargin[Math.min(2, depth / 8)];
        
        const moves = position.generateMoves();
        position.moveOrdering.orderMoves(moves, null, depth, position);
        
        for (const move of moves) {
            if (!position.see(move, -probCutBeta + beta)) continue;
            
            const undo = position.makeMove(move);
            const score = -await position.search(probCutDepth, -probCutBeta, -probCutBeta + 1, true);
            position.undoMove(move, undo);
            
            if (score >= probCutBeta) return score;
        }
        
        return -position.INFINITY;
    }
}

class ParallelSearch {
    constructor(engine) {
        this.engine = engine;
        this.workers = [];
    }

    async init() {
        if (typeof Worker === 'undefined') return;
        
        const workerCount = Math.min(navigator.hardwareConcurrency - 1, 4);
        for (let i = 0; i < workerCount; i++) {
            const worker = new Worker('engine-worker.js');
            worker.onmessage = this.handleWorkerMessage.bind(this);
            this.workers.push(worker);
        }
    }

    handleWorkerMessage(e) {
        if (e.data.type === 'bestmove') {
            this.engine.stopSearch = true;
        }
    }

    async search(depth) {
        if (this.workers.length === 0) {
            return this.engine.search(depth, -this.engine.INFINITY, this.engine.INFINITY, false, true);
        }

        const promises = this.workers.map(worker => {
            return new Promise(resolve => {
                const handler = (e) => {
                    worker.removeEventListener('message', handler);
                    resolve(e.data);
                };
                worker.addEventListener('message', handler);
                worker.postMessage({
                    type: 'search',
                    depth: depth - 2 + Math.random() // Randomized depth for diversity
                });
            });
        });

        const results = await Promise.all(promises);
        return results.reduce((best, r) => r.score > best.score ? r : best);
    }
}

class SyzygyTablebases {
    constructor(maxPieces = 7) {
        this.maxPieces = maxPieces;
        this.ready = false;
    }

    async init() {
        try {
            // In a real implementation, this would load the tablebase files
            this.ready = true;
        } catch (e) {
            console.error("Syzygy initialization failed:", e);
            this.ready = false;
        }
    }

    probe(position) {
        if (!this.ready || position.popCount(position.occupancy[2]) > this.maxPieces) {
            return null;
        }

        // Simplified for demonstration - in a real implementation this would probe the tablebases
        return null;
    }
}

class PawnStructureCache {
    constructor() {
        this.cache = new Map();
        this.hashMask = (1n << 64n) - 1n;
    }

    evaluate(position) {
        const key = position.hash & this.hashMask;
        if (this.cache.has(key)) {
            return this.cache.get(key);
        }

        let score = 0;
        score += this.evalPawnStructure(position, position.WHITE);
        score -= this.evalPawnStructure(position, position.BLACK);
        
        this.cache.set(key, score);
        return score;
    }

    evalPawnStructure(position, color) {
        const pawns = position.bitboards[color * 6 + position.PAWN - 1];
        let score = 0;
        
        // Doubled pawns
        for (let file = 0; file < 8; file++) {
            const filePawns = pawns & position.fileMasks[file];
            const count = position.popCount(filePawns);
            if (count > 1) score -= 20 * (count - 1);
        }
        
        // Isolated pawns
        let isolated = pawns;
        while (isolated) {
            const sq = position.bitScanForward(isolated);
            isolated &= isolated - 1n;
            
            const file = sq % 8;
            if (!(pawns & position.isolatedMask[file])) {
                score -= 15;
            }
        }
        
        // Passed pawns
        let passed = pawns;
        while (passed) {
            const sq = position.bitScanForward(passed);
            passed &= passed - 1n;
            
            if (!(position.bitboards[(color ^ 1) * 6 + position.PAWN - 1] & 
                position.passedPawnMasks[color][sq])) {
                const rank = Math.floor(sq / 8);
                const promotionDist = color === position.WHITE ? 7 - rank : rank;
                score += 30 + (6 - promotionDist) * 15;
            }
        }
        
        // Pawn chains
        let chains = pawns;
        while (chains) {
            const sq = position.bitScanForward(chains);
            chains &= chains - 1n;
            
            const file = sq % 8;
            const rank = Math.floor(sq / 8);
            
            // Check for supporting pawns
            if (file > 0 && (pawns & (1n << BigInt(sq + (color === position.WHITE ? 7 : -9)))) {
                score += 10;
            }
            if (file < 7 && (pawns & (1n << BigInt(sq + (color === position.WHITE ? 9 : -7)))) {
                score += 10;
            }
        }
        
        return score;
    }
}

class LearningBook {
    constructor() {
        this.book = new Map();
        this.ready = false;
    }

    async load(url) {
        try {
            // In a real implementation, this would load an opening book
            // For now we'll just add some basic openings
            this.addBookMove("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", "e2e4");
            this.addBookMove("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", "d2d4");
            this.addBookMove("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1", "e7e5");
            this.ready = true;
        } catch (e) {
            console.error("Opening book loading failed:", e);
            this.ready = false;
        }
    }

    addBookMove(fen, move) {
        if (!this.book.has(fen)) {
            this.book.set(fen, []);
        }
        this.book.get(fen).push(move);
    }

    getMove(fen) {
        if (!this.ready || !this.book.has(fen)) return null;
        
        const moves = this.book.get(fen);
        if (moves.length === 0) return null;
        
        // Return a random book move
        return moves[Math.floor(Math.random() * moves.length)];
    }
}
class AdvancedSearchExtensions {
    constructor(engine) {
        this.engine = engine;
        this.threatTable = new Int16Array(64 * 64);
    }

    shouldExtend(depth, move, position) {
        let extension = 0;
        
        // Check extensions (more aggressive in deep searches)
        if (this.givesCheck(move, position)) {
            extension = 1 + (depth < 8 ? 1 : 0);
        }
        
        // Singular extension (from Stockfish)
        if (depth >= 8 && !extension && this.isSingular(position, move, depth)) {
            extension = 1;
        }
        
        // Pawn push near promotion
        if (move.piece === position.PAWN) {
            const rank = Math.floor(move.to / 8);
            if ((position.side === position.WHITE && rank >= 4) || 
                (position.side === position.BLACK && rank <= 3)) {
                extension = Math.max(extension, 1);
            }
        }
        
        return extension;
    }

    isSingular(position, move, depth) {
        const tt = position.probeTT();
        if (!tt || tt.depth < depth - 3 || tt.move === null) return false;
        
        const singularBeta = tt.score - 3 * depth;
        position.makeNullMove();
        const score = -position.search(depth / 2, -singularBeta, -singularBeta + 1, false);
        position.undoNullMove();
        
        return score < singularBeta;
    }
}

class AdvancedPruning {
    constructor() {
        this.historyCutoff = new Int16Array(2 * 64 * 64);
    }

    shouldPrune(position, move, depth, improving) {
        // Futility pruning
        if (depth <= 7 && !improving && !move.captured && !move.promotion) {
            const margin = 150 + 175 * depth - 50 * position.evaluator.getPositionality(position);
            if (position.evaluate() + margin <= position.alpha) {
                return true;
            }
        }
        
        // History pruning
        if (depth <= 4 && !move.captured && !move.promotion) {
            const history = this.historyCutoff[position.side * 4096 + move.from * 64 + move.to];
            if (history < depth * depth * 2) {
                return true;
            }
        }
        
        return false;
    }

    updateHistory(move, depth, success, position) {
        const index = position.side * 4096 + move.from * 64 + move.to;
        const delta = success ? depth * depth : -depth * depth;
        this.historyCutoff[index] = Math.max(-32767, Math.min(32767, this.historyCutoff[index] + delta));
    }
}

class EnhancedMoveOrdering {
    // Add to your existing move ordering class
    orderMoves(moves, ttMove, depth, position) {
        const prevMove = position.stack.length > 0 ? 
            position.stack[position.stack.length - 1].move : null;
        const prevPrevMove = position.stack.length > 1 ? 
            position.stack[position.stack.length - 2].move : null;

        for (const move of moves) {
            let score = 0;
            
            // TT move gets highest priority
            if (ttMove && move.from === ttMove.from && move.to === ttMove.to) {
                score = 1000000;
            }
            // Winning captures (SEE positive)
            else if (move.captured && position.see(move, 0)) {
                score = 90000 + this.captureValue(move, position);
            }
            // Killer moves
            else if (move === position.killers[0][position.ply]) {
                score = 80000;
            }
            else if (move === position.killers[1][position.ply]) {
                score = 70000;
            }
            // Counter moves
            else if (prevMove && this.counterMoves[prevMove.piece][prevMove.to] && 
                     this.isSameMove(move, this.counterMoves[prevMove.piece][prevMove.to])) {
                score = 60000;
            }
            // Follow-up moves
            else if (prevPrevMove && this.followupMoves[prevPrevMove.piece][prevPrevMove.to] && 
                     this.isSameMove(move, this.followupMoves[prevPrevMove.piece][prevPrevMove.to])) {
                score = 50000;
            }
            // History heuristic with butterfly
            else {
                score = position.historyHeuristic[position.side][move.from][move.piece][move.to] + 
                        position.butterfly[move.from][move.to] / 2;
                
                // Add bonus for threatening squares
                score += this.threatBonus(move, position);
            }
            
            // Promotion bonus (higher for queen promotions)
            if (move.flags === position.FLAGS.PROMOTION) {
                score += 50000 + (move.promotion === position.QUEEN ? 200 : 100);
            }
            
            // Check bonus
            if (this.givesCheck(move, position)) score += 30000;
            
            // Pawn push bonus in endgame
            if (move.piece === position.PAWN) {
                const phase = position.gamePhase() / 256;
                if (phase > 0.6) {
                    const rank = Math.floor(move.to / 8);
                    const promotionDist = position.side === position.WHITE ? 7 - rank : rank;
                    score += (6 - promotionDist) * 20;
                }
            }
            
            move.score = score;
        }
        
        moves.sort((a, b) => b.score - a.score);
    }

    captureValue(move, position) {
        // MVV-LVA with SEE refinement
        let value = position.pieceValue(move.captured) * 10 - position.pieceValue(move.piece);
        
        // Add bonus for capturing with less valuable pieces
        if (position.pieceValue(move.piece) < position.pieceValue(move.captured)) {
            value += 50;
        }
        
        // Add bonus for recaptures
        if (position.stack.length > 0) {
            const lastMove = position.stack[position.stack.length - 1].move;
            if (lastMove && lastMove.to === move.to) {
                value += 30;
            }
        }
        
        return value;
    }

    threatBonus(move, position) {
        let bonus = 0;
        const undo = position.makeMove(move);
        
        // Bonus for discovered attacks
        const us = position.side;
        const them = us ^ 1;
        const fromBB = 1n << BigInt(move.from);
        
        // Check for discovered checks
        const kingSquare = position.bitScanForward(position.bitboards[them * 6 + position.KING - 1]);
        if (kingSquare >= 0) {
            const oldAttacks = position.getAttackers(kingSquare, position.occupancy[2] | fromBB, them, us);
            const newAttacks = position.getAttackers(kingSquare, position.occupancy[2], them, us);
            
            if (newAttacks > oldAttacks) {
                bonus += 150;
            }
        }
        
        // Bonus for creating multiple threats
        let threats = 0;
        for (let piece = position.PAWN; piece <= position.QUEEN; piece++) {
            let bb = position.bitboards[them * 6 + piece - 1];
            while (bb) {
                const sq = position.bitScanForward(bb);
                bb &= bb - 1n;
                
                if (position.isSquareAttacked(sq, us)) {
                    threats++;
                }
            }
        }
        
        if (threats > 1) bonus += threats * 30;
        
        position.undoMove(move, undo);
        return bonus;
    }
}



class EnhancedTimeManager {
    // Replace your existing time manager with this
    init(timeLeft, increment, movesToGo, position) {
        const phase = position.gamePhase() / 256;
        const complexity = this.calculateComplexity(position);
        const materialDiff = Math.abs(position.evaluator.evalMaterial(position, 0));
        
        // Base time calculation with dynamic adjustments
        const expectedMoves = movesToGo || (28 - phase * 10);
        let baseTime = timeLeft / expectedMoves;
        
        // Add increment
        baseTime += increment * 0.8;
        
        // Adjust for game phase (spend more time in middlegame)
        this.timeBudget = baseTime * (1.3 - phase * 0.3);
        
        // Adjust for position complexity
        this.timeBudget *= (1.0 + complexity * 0.4);
        
        // Adjust for material imbalance (spend more time in sharp positions)
        this.timeBudget *= (1.0 + Math.min(0.5, materialDiff / 800));
        
        // Minimum time to avoid instant moves
        this.timeBudget = Math.max(50, this.timeBudget);
        
        // Panic time is 20% of budget or 10% of remaining, whichever is smaller
        this.panicTime = Math.min(timeLeft * 0.1, this.timeBudget * 0.2);
        
        // Node limit based on time control
        this.maxNodes = timeLeft < 30000 ? 1e6 : 5e6;
        
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.bestMoveChanges = 0;
    }

    shouldStop(elapsed, depth, score, nodes) {
        // Always finish current depth if we're in panic mode
        if (elapsed > this.panicTime && depth > 1) {
            return true;
        }
        
        // Node limit
        if (nodes >= this.maxNodes) return true;
        
        // Score drop detection
        if (score < this.lastScore - 100) {
            this.scoreDrops++;
            if (this.scoreDrops >= 2 && elapsed > this.timeBudget * 0.3) {
                return true;
            }
        }
        
        // Best move stability check
        if (depth >= 6 && Math.abs(score - this.lastScore) < 20) {
            this.bestMoveChanges++;
            if (this.bestMoveChanges >= 3 && elapsed > this.timeBudget * 0.5) {
                return true;
            }
        }
        
        this.lastScore = score;
        return elapsed >= this.timeBudget;
    }
}


// ===================== COMPLETE ENDGAME KNOWLEDGE =====================
class EndgameKnowledge {
    constructor() {
        this.SCALE_FACTORS = new Map([
            ['KPK', 0.8],
            ['KBNK', 1.0],
            ['KRKP', 0.7]
        ]);
    }

    evaluate(position) {
        const material = position.evaluator.evalMaterial(position, 1);
        const phase = position.gamePhase() / 256;
        
        if (phase > 0.5) return 0; // Only apply in endgame
        
        let score = 0;
        score += this.evalKPK(position, material);
        score += this.evalKBNK(position, material);
        score += this.evalKRKP(position, material);
        
        return score * phase;
    }

    evalKPK(position, material) {
        const us = position.side;
        const them = us ^ 1;
        
        // Check if this is a KPK endgame
        const whitePieces = position.popCount(position.bitboards[position.COLORS.WHITE * 6]);
        const blackPieces = position.popCount(position.bitboards[position.COLORS.BLACK * 6]);
        
        if (whitePieces !== 1 || blackPieces !== 1) return 0;
        
        const whitePawns = position.popCount(position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.PAWN - 1]);
        const blackPawns = position.popCount(position.bitboards[position.COLORS.BLACK * 6 + position.PIECE_TYPES.PAWN - 1]);
        
        if ((whitePawns !== 1 || blackPawns !== 0) && 
            (blackPawns !== 1 || whitePawns !== 0)) return 0;
            
        const strongSide = whitePawns === 1 ? position.COLORS.WHITE : position.COLORS.BLACK;
        const weakSide = 1 - strongSide;
        
        const pawnSquare = position.bitScanForward(
            position.bitboards[strongSide * 6 + position.PIECE_TYPES.PAWN - 1]
        );
        const strongKing = position.bitScanForward(
            position.bitboards[strongSide * 6 + position.PIECE_TYPES.KING - 1]
        );
        const weakKing = position.bitScanForward(
            position.bitboards[weakSide * 6 + position.PIECE_TYPES.KING - 1]
        );
        
        if (pawnSquare === -1 || strongKing === -1 || weakKing === -1) return 0;
        
        const pawnFile = pawnSquare % 8;
        const pawnRank = Math.floor(pawnSquare / 8);
        const strongKingFile = strongKing % 8;
        const strongKingRank = Math.floor(strongKing / 8);
        const weakKingFile = weakKing % 8;
        const weakKingRank = Math.floor(weakKing / 8);
        
        // Rule of the square
        const promotionRank = strongSide === position.COLORS.WHITE ? 7 : 0;
        const promotionSquare = pawnFile + promotionRank * 8;
        const distToPromotion = Math.abs(promotionRank - pawnRank);
        
        // Key squares: 2 squares in front of the pawn
        const keySquares = [
            pawnSquare + (strongSide === position.COLORS.WHITE ? 16 : -16),
            pawnSquare + (strongSide === position.COLORS.WHITE ? 16 : -16) + 1,
            pawnSquare + (strongSide === position.COLORS.WHITE ? 16 : -16) - 1
        ].filter(sq => sq >= 0 && sq < 64);
        
        // Check if pawn can be promoted
        let result = 0;
        if (strongSide === position.COLORS.WHITE) {
            // White to move
            if (position.side === strongSide) {
                if (pawnRank === 6) {
                    // About to promote
                    if (Math.abs(weakKingFile - pawnFile) > 1 || 
                        weakKingRank < 6) {
                        result = 500; // Winning position
                    }
                } else if (keySquares.some(sq => sq === strongKing)) {
                    // King controls key squares
                    result = 200 + (6 - pawnRank) * 50;
                }
            } else {
                // Black to move - can it stop the pawn?
                if (Math.abs(weakKingFile - pawnFile) <= 1 && 
                    weakKingRank >= pawnRank && 
                    weakKingRank <= pawnRank + 1) {
                    result = -100; // Drawn position
                }
            }
        } else {
            // Black to move (with pawn)
            if (position.side === strongSide) {
                if (pawnRank === 1) {
                    // About to promote
                    if (Math.abs(weakKingFile - pawnFile) > 1 || 
                        weakKingRank > 1) {
                        result = 500; // Winning position
                    }
                } else if (keySquares.some(sq => sq === strongKing)) {
                    // King controls key squares
                    result = 200 + (pawnRank) * 50;
                }
            } else {
                // White to move - can it stop the pawn?
                if (Math.abs(weakKingFile - pawnFile) <= 1 && 
                    weakKingRank <= pawnRank && 
                    weakKingRank >= pawnRank - 1) {
                    result = -100; // Drawn position
                }
            }
        }
        
        return strongSide === position.side ? result : -result;
    }

    evalKBNK(position, material) {
        // Check if this is a KBNK endgame
        const whitePieces = position.popCount(position.bitboards[position.COLORS.WHITE * 6]);
        const blackPieces = position.popCount(position.bitboards[position.COLORS.BLACK * 6]);
        
        if (whitePieces !== 2 || blackPieces !== 1) return 0;
        
        const whiteBishops = position.popCount(
            position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.BISHOP - 1]
        );
        const whiteKnights = position.popCount(
            position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.KNIGHT - 1]
        );
        
        if (whiteBishops !== 1 || whiteKnights !== 1) return 0;
        
        // This is a forced win, but difficult to execute
        // Return a high score but not quite mate score
        return position.side === position.COLORS.WHITE ? 800 : -800;
    }

    evalKRKP(position, material) {
        // Check if this is a KRKP endgame
        const whitePieces = position.popCount(position.bitboards[position.COLORS.WHITE * 6]);
        const blackPieces = position.popCount(position.bitboards[position.COLORS.BLACK * 6]);
        
        if ((whitePieces !== 2 || blackPieces !== 1) && 
            (blackPieces !== 2 || whitePieces !== 1)) return 0;
            
        let strongSide, weakSide;
        let rookPos, pawnPos;
        
        if (whitePieces === 2) {
            strongSide = position.COLORS.WHITE;
            weakSide = position.COLORS.BLACK;
            rookPos = position.bitScanForward(
                position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.ROOK - 1]
            );
            pawnPos = position.bitScanForward(
                position.bitboards[position.COLORS.BLACK * 6 + position.PIECE_TYPES.PAWN - 1]
            );
        } else {
            strongSide = position.COLORS.BLACK;
            weakSide = position.COLORS.WHITE;
            rookPos = position.bitScanForward(
                position.bitboards[position.COLORS.BLACK * 6 + position.PIECE_TYPES.ROOK - 1]
            );
            pawnPos = position.bitScanForward(
                position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.PAWN - 1]
            );
        }
        
        if (rookPos === -1 || pawnPos === -1) return 0;
        
        const strongKing = position.bitScanForward(
            position.bitboards[strongSide * 6 + position.PIECE_TYPES.KING - 1]
        );
        const weakKing = position.bitScanForward(
            position.bitboards[weakSide * 6 + position.PIECE_TYPES.KING - 1]
        );
        
        if (strongKing === -1 || weakKing === -1) return 0;
        
        const pawnFile = pawnPos % 8;
        const pawnRank = Math.floor(pawnPos / 8);
        const promotionRank = weakSide === position.COLORS.WHITE ? 7 : 0;
        
        // Basic rules for KRKP:
        // 1. If pawn is not too far advanced and king is close, it's a win
        // 2. If pawn is on 7th rank with king behind it, it's often a draw
        let result = 0;
        
        if (strongSide === position.COLORS.WHITE) {
            if (pawnRank <= 3) {
                // Pawn not too advanced - winning position
                result = 300;
            } else if (pawnRank >= 5) {
                // Advanced pawn - check if king can catch it
                const dist = Math.abs(Math.floor(strongKing / 8) - pawnRank);
                if (dist <= 1) {
                    result = 200;
                } else {
                    // Drawish position
                    result = 50;
                }
            }
        } else {
            // Black is strong side
            if (pawnRank >= 4) {
                // Pawn not too advanced - winning position
                result = 300;
            } else if (pawnRank <= 2) {
                // Advanced pawn - check if king can catch it
                const dist = Math.abs(Math.floor(strongKing / 8) - pawnRank);
                if (dist <= 1) {
                    result = 200;
                } else {
                    // Drawish position
                    result = 50;
                }
            }
        }
        
        // Bonus if rook is behind the pawn
        const rookRank = Math.floor(rookPos / 8);
        if ((strongSide === position.COLORS.WHITE && rookRank > pawnRank) ||
            (strongSide === position.COLORS.BLACK && rookRank < pawnRank)) {
            result += 50;
        }
        
        return strongSide === position.side ? result : -result;
    }
}


    // ===================== UCI PROTOCOL IMPLEMENTATION =====================
    async handleUCICommand(command) {
        const parts = command.trim().split(/\s+/);
        const cmd = parts[0].toLowerCase();

        try {
            switch(cmd) {
                case 'uci':
                    return this.uciIdentify();
                case 'isready':
                    return 'readyok';
                case 'ucinewgame':
                    this.resetGame();
                    return '';
                case 'position':
                    return this.handlePositionCommand(parts.slice(1));
                case 'go':
                    return this.handleGoCommand(parts.slice(1));
                case 'stop':
                    this.stopSearch = true;
                    return '';
                case 'quit':
                    this.stopSearch = true;
                    if (typeof process !== 'undefined') process.exit(0);
                    return '';
                case 'setoption':
                    return this.handleSetOption(parts.slice(1));
                default:
                    return `Unknown command: ${cmd}`;
            }
        } catch (e) {
            return `error ${e.message}`;
        }
    }

    uciIdentify() {
        return [
            'id name SKY5L V8',
            'id author Your Name',
            'option name Hash type spin default 128 min 1 max 2048',
            'option name Contempt type spin default 0 min -100 max 100',
            'option name SyzygyPath type string default <empty>',
            'option name Threads type spin default 1 min 1 max 128',
            'uciok'
        ].join('\n');
    }

    handlePositionCommand(args) {
        let idx = 0;
        if (args[idx] === 'startpos') {
            this.setPosition('rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1');
            idx++;
        } else if (args[idx] === 'fen') {
            const fen = args.slice(1, 7).join(' ');
            this.setPosition(fen);
            idx = 7;
        } else {
            throw new Error('Invalid position command');
        }

        if (args[idx] === 'moves') {
            for (let i = idx + 1; i < args.length; i++) {
                const move = this.parseUCIMove(args[i]);
                if (!move) throw new Error(`Invalid move: ${args[i]}`);
                this.makeMove(move);
            }
        }

        return '';
    }

    async handleGoCommand(args) {
        const limits = {};
        for (let i = 0; i < args.length; i++) {
            switch(args[i]) {
                case 'wtime': limits.wtime = parseInt(args[++i]); break;
                case 'btime': limits.btime = parseInt(args[++i]); break;
                case 'winc': limits.winc = parseInt(args[++i]); break;
                case 'binc': limits.binc = parseInt(args[++i]); break;
                case 'movestogo': limits.movestogo = parseInt(args[++i]); break;
                case 'depth': limits.depth = parseInt(args[++i]); break;
                case 'nodes': limits.nodes = parseInt(args[++i]); break;
                case 'movetime': limits.movetime = parseInt(args[++i]); break;
                case 'infinite': limits.infinite = true; break;
            }
        }

        this.stopSearch = false;
        const bestMove = await this.getBestMove(limits);
        return `bestmove ${this.moveToUCI(bestMove)}`;
    }

    parseUCIMove(uciMove) {
        if (uciMove.length < 4) return null;
        
        const from = this.squareToIndex(uciMove.substring(0, 2));
        const to = this.squareToIndex(uciMove.substring(2, 4));
        if (from < 0 || to < 0) return null;

        const moves = this.generateMoves();
        for (const move of moves) {
            if (move.from === from && move.to === to) {
                // Handle promotion
                if (uciMove.length === 5) {
                    const promo = uciMove[4].toLowerCase();
                    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
                        const promoPieces = {q: this.PIECE_TYPES.QUEEN, r: this.PIECE_TYPES.ROOK, 
                                           b: this.PIECE_TYPES.BISHOP, n: this.PIECE_TYPES.KNIGHT};
                        if (promoPieces[promo] && move.promotion === promoPieces[promo]) {
                            return move;
                        }
                    }
                } else if (move.flags !== this.MOVE_FLAGS.PROMOTION) {
                    return move;
                }
            }
        }
        return null;
    }

    moveToUCI(move) {
        if (!move) return '0000'; // Null move
        const files = 'abcdefgh';
        const ranks = '12345678';
        const from = files[move.from % 8] + ranks[7 - Math.floor(move.from / 8)];
        const to = files[move.to % 8] + ranks[7 - Math.floor(move.to / 8)];
        
        if (move.flags === this.MOVE_FLAGS.PROMOTION) {
            const promo = {[this.PIECE_TYPES.QUEEN]: 'q', [this.PIECE_TYPES.ROOK]: 'r',
                          [this.PIECE_TYPES.BISHOP]: 'b', [this.PIECE_TYPES.KNIGHT]: 'n'};
            return from + to + promo[move.promotion];
        }
        return from + to;
    }


}


// ===================== UCI INTERFACE =====================
class UCIInterface {
    constructor(engine) {
        this.engine = engine;
        this.isReady = false;
        
        if (typeof process !== 'undefined') {
            // Node.js environment
            process.stdin.on('data', (data) => this.processInput(data.toString()));
            this.send = (msg) => process.stdout.write(msg + '\n');
        } else {
            // Browser/Web Worker environment
            this.send = (msg) => postMessage({type: 'uci', message: msg});
            onmessage = (e) => this.processInput(e.data);
        }
    }

    processInput(input) {
        input.trim().split('\n').forEach(line => {
            const response = this.engine.handleUCICommand(line);
            if (response) this.send(response);
        });
    }
}

// Initialize the engine and UCI interface
const engine = new SKY5LChess();
engine.init().then(() => {
    if (typeof process !== 'undefined' || typeof postMessage !== 'undefined') {
        new UCIInterface(engine);
    }
});




// Export for Node.js and browser
if (typeof module !== 'undefined') module.exports = SKY5LChess;
if (typeof window !== 'undefined') window.SKY5LChess = SKY5LChess;


