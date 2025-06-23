// ================ SKY5L CHESS ENGINE =====================


class SKY5LChess {
  constructor() {
    // Constants
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
    
    // Optimized piece values [middlegame, endgame]
    this.PIECE_VALUES = [
      [0, 0],       // None
      [105, 140],   // Pawn
      [325, 370],   // Knight
      [345, 390],   // Bishop
      [550, 610],   // Rook
      [1020, 1080], // Queen
      [20000, 20000] // King
    ];

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
    this.MAX_DEPTH = 64;
    this.TT_SIZE_MB = 128;
    this.SYZYGY_MAX_PIECES = 6;
    this.THREADS = 4;
    
    this.killers = Array.from({length: 2}, () => new Array(this.MAX_DEPTH).fill(null));
    this.historyHeuristic = new Int32Array(12 * 64 * 12 * 64);
    this.butterfly = new Int32Array(64 * 64);
    this.initTranspositionTable(this.TT_SIZE_MB);
    this.nodes = 0;
    this.startTime = 0;
    this.stopSearch = false;
    this.seldepth = 0;
    this.searching = false;
    this.lastScore = 0;
    this.scoreDrops = 0;
    this.pvTable = new Array(this.MAX_DEPTH).fill().map(() => new Array(this.MAX_DEPTH).fill(null));
    
    // Evaluation components
    this.initPieceSquareTables();
    this.initAttackTables();
    this.initEvaluationMasks();
    this.initMagicBitboards();
    this.initZobrist();
    
    // Initialize with standard position
    this.setPosition("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
  }

  // ===================== INITIALIZATION =====================
  async init() {
    // Load any required resources (NNUE, tablebases, etc.)
    return Promise.resolve();
  }

  initTranspositionTable(sizeMB = 128) {
    const sizeEntries = Math.floor((sizeMB * 1024 * 1024) / 24);
    this.transpositionTable = new Array(sizeEntries);
    this.ttMask = sizeEntries - 1;
    this.ttGeneration = 0;
  }

  initPieceSquareTables() {
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
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.PAWN - 1][i] = tables.pawn[i];
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.KNIGHT - 1][i] = tables.knight[i];
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.BISHOP - 1][i] = tables.bishop[i];
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.ROOK - 1][i] = tables.rook[i];
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.QUEEN - 1][i] = tables.queen[i];
      this.pst[this.COLORS.WHITE * 6 + this.PIECE_TYPES.KING - 1][i] = tables.king[i];
      
      // Black pieces (mirrored vertically)
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.PAWN - 1][63 - i] = -tables.pawn[i];
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.KNIGHT - 1][63 - i] = -tables.knight[i];
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.BISHOP - 1][63 - i] = -tables.bishop[i];
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.ROOK - 1][63 - i] = -tables.rook[i];
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.QUEEN - 1][63 - i] = -tables.queen[i];
      this.pst[this.COLORS.BLACK * 6 + this.PIECE_TYPES.KING - 1][63 - i] = -tables.king[i];
    }
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
        if (square % 8 > 0) this.pawnAttacks[this.COLORS.WHITE][square] |= 1n << BigInt(square - 9);
        if (square % 8 < 7) this.pawnAttacks[this.COLORS.WHITE][square] |= 1n << BigInt(square - 7);
      }
      if (square < 56) { // Black pawns
        if (square % 8 > 0) this.pawnAttacks[this.COLORS.BLACK][square] |= 1n << BigInt(square + 7);
        if (square % 8 < 7) this.pawnAttacks[this.COLORS.BLACK][square] |= 1n << BigInt(square + 9);
      }
    }
  }

  initEvaluationMasks() {
    // File masks
    this.fileMasks = new Array(8);
    for (let file = 0; file < 8; file++) {
      this.fileMasks[file] = 0x0101010101010101n << BigInt(file);
    }

    // Passed pawn masks
    this.passedPawnMasks = Array.from({length: 2}, () => new Array(64).fill(0n));
    for (let sq = 0; sq < 64; sq++) {
      const file = sq % 8;
      const rank = Math.floor(sq / 8);
      
      // White passed pawn mask
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
      this.passedPawnMasks[this.COLORS.BLACK][sq] = whiteMask;
      
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
      this.passedPawnMasks[this.COLORS.WHITE][sq] = blackMask;
    }

    // Isolated pawn masks
    this.isolatedMask = new Array(8).fill(0n);
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

    // King safety masks
    this.kingSafetyMask = new Array(64).fill(0n);
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
        }
      }
      this.kingSafetyMask[sq] = mask;
    }
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

  // ===================== POSITION MANAGEMENT =====================
  setPosition(fen) {
    // Reset board
    this.bitboards.fill(0n);
    this.occupancy.fill(0n);
    
    const parts = fen.split(' ');
    if (parts.length < 4) return false;
    
    // Parse piece placement
    const rows = parts[0].split('/');
    if (rows.length !== 8) return false;
    
    for (let rank = 0; rank < 8; rank++) {
      let file = 0;
      for (const c of rows[rank]) {
        if (c >= '1' && c <= '8') {
          file += parseInt(c);
        } else {
          const piece = this.charToPiece(c);
          if (!piece) return false;
          
          const square = rank * 8 + file;
          this.bitboards[piece.color * 6 + piece.type - 1] |= 1n << BigInt(square);
          this.occupancy[piece.color] |= 1n << BigInt(square);
          this.occupancy[2] |= 1n << BigInt(square);
          file++;
        }
      }
    }
    
    // Parse active color
    this.side = parts[1] === 'w' ? this.COLORS.WHITE : this.COLORS.BLACK;
    
    // Parse castling rights
    this.castling = 0;
    if (parts[2] !== '-') {
      for (const c of parts[2]) {
        switch (c) {
          case 'K': this.castling |= 0b0001; break;
          case 'Q': this.castling |= 0b0010; break;
          case 'k': this.castling |= 0b0100; break;
          case 'q': this.castling |= 0b1000; break;
        }
      }
    }
    
    // Parse en passant
    this.epSquare = parts[3] === '-' ? -1 : 
      (parts[3].charCodeAt(0) - 'a'.charCodeAt(0)) + 
      (8 - parseInt(parts[3][1])) * 8;
    
    // Parse halfmove clock and fullmove number
    this.halfmoveClock = parts.length > 4 ? parseInt(parts[4]) : 0;
    this.fullmoveNumber = parts.length > 5 ? parseInt(parts[5]) : 1;
    
    // Update hash
    this.updateHash();
    
    return true;
  }

  charToPiece(c) {
    const lower = c.toLowerCase();
    const color = c === lower ? this.COLORS.BLACK : this.COLORS.WHITE;
    
    switch (lower) {
      case 'p': return { type: this.PIECE_TYPES.PAWN, color };
      case 'n': return { type: this.PIECE_TYPES.KNIGHT, color };
      case 'b': return { type: this.PIECE_TYPES.BISHOP, color };
      case 'r': return { type: this.PIECE_TYPES.ROOK, color };
      case 'q': return { type: this.PIECE_TYPES.QUEEN, color };
      case 'k': return { type: this.PIECE_TYPES.KING, color };
      default: return null;
    }
  }

  updateHash() {
    this.hash = 0n;
    
    // Piece positions
    for (let i = 0; i < 12; i++) {
      let bb = this.bitboards[i];
      while (bb) {
        const sq = this.bitScanForward(bb);
        bb &= bb - 1n;
        this.hash ^= this.zobrist.pieces[i][sq];
      }
    }
    
    // Side to move
    if (this.side === this.COLORS.WHITE) {
      this.hash ^= this.zobrist.side;
    }
    
    // Castling rights
    this.hash ^= this.zobrist.castling[this.castling];
    
    // En passant
    if (this.epSquare >= 0) {
      this.hash ^= this.zobrist.ep[this.epSquare];
    }
  }

  getFEN() {
    let fen = '';
    
    // Piece placement
    for (let rank = 0; rank < 8; rank++) {
      let empty = 0;
      
      for (let file = 0; file < 8; file++) {
        const square = rank * 8 + file;
        let piece = null;
        
        for (let i = 0; i < 12; i++) {
          if (this.bitboards[i] & (1n << BigInt(square))) {
            piece = i;
            break;
          }
        }
        
        if (piece === null) {
          empty++;
        } else {
          if (empty > 0) {
            fen += empty;
            empty = 0;
          }
          fen += this.pieceToChar(piece);
        }
      }
      
      if (empty > 0) {
        fen += empty;
      }
      
      if (rank < 7) {
        fen += '/';
      }
    }
    
    // Active color
    fen += this.side === this.COLORS.WHITE ? ' w ' : ' b ';
    
    // Castling rights
    let castling = '';
    if (this.castling & 0b0001) castling += 'K';
    if (this.castling & 0b0010) castling += 'Q';
    if (this.castling & 0b0100) castling += 'k';
    if (this.castling & 0b1000) castling += 'q';
    fen += castling || '-';
    
    // En passant
    fen += ' ';
    if (this.epSquare >= 0) {
      const file = this.epSquare % 8;
      const rank = Math.floor(this.epSquare / 8);
      fen += String.fromCharCode('a'.charCodeAt(0) + file) + (8 - rank);
    } else {
      fen += '-';
    }
    
    // Halfmove clock and fullmove number
    fen += ` ${this.halfmoveClock} ${this.fullmoveNumber}`;
    
    return fen;
  }

  pieceToChar(pieceIndex) {
    const color = Math.floor(pieceIndex / 6);
    const type = (pieceIndex % 6) + 1;
    
    const pieces = ['', 'P', 'N', 'B', 'R', 'Q', 'K'];
    const c = pieces[type];
    return color === this.COLORS.WHITE ? c : c.toLowerCase();
  }

  // ===================== MOVE GENERATION =====================
  generateMoves() {
    const moves = [];
    const us = this.side;
    const them = us ^ 1;
    const kingSquare = this.bitScanForward(
      this.bitboards[us * 6 + this.PIECE_TYPES.KING - 1]
    );
    
    // Detect pins and checks
    const { pinnedPieces, checkers } = this.detectPinsAndChecks(kingSquare, us);
    const inCheck = checkers !== 0n;
    const doubleCheck = this.popCount(checkers) > 1;
    
    // Generate moves based on game state
    if (inCheck) {
      this.generateEvasions(moves, kingSquare, checkers, pinnedPieces, doubleCheck);
    } else {
      this.generateQuietMoves(moves, kingSquare, pinnedPieces);
      this.generateCaptures(moves, kingSquare, pinnedPieces);
      this.generateSpecialMoves(moves, kingSquare, pinnedPieces);
    }

    return moves;
  }

  detectPinsAndChecks(kingSquare, color) {
    const them = color ^ 1;
    const pinnedPieces = 0n;
    const checkers = 0n;
    
    // Check for sliding piece checks/pins
    const sliders = this.bitboards[them * 6 + this.PIECE_TYPES.QUEEN - 1] |
                   this.bitboards[them * 6 + this.PIECE_TYPES.ROOK - 1] |
                   this.bitboards[them * 6 + this.PIECE_TYPES.BISHOP - 1];
    
    let sliderBB = sliders;
    while (sliderBB) {
      const sq = this.bitScanForward(sliderBB);
      sliderBB &= sliderBB - 1n;
      
      const pieceType = this.getPieceAt(sq, them);
      const attacks = this.getSliderAttacks(pieceType, sq);
      
      // If the slider attacks the king, it's a checker
      if (attacks & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    // Check for knight checks
    let knights = this.bitboards[them * 6 + this.PIECE_TYPES.KNIGHT - 1];
    while (knights) {
      const sq = this.bitScanForward(knights);
      knights &= knights - 1n;
      
      if (this.knightAttacks[sq] & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    // Check for pawn checks
    let pawns = this.bitboards[them * 6 + this.PIECE_TYPES.PAWN - 1];
    while (pawns) {
      const sq = this.bitScanForward(pawns);
      pawns &= pawns - 1n;
      
      if (this.pawnAttacks[them][sq] & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    return { pinnedPieces, checkers };
  }

  generateEvasions(moves, kingSquare, checkers, pinnedPieces, doubleCheck) {
    const us = this.side;
    const them = us ^ 1;
    
    // King moves - must move out of attack
    this.generateKingMoves(moves, kingSquare, true);
    
    // If double check, only king moves are legal
    if (doubleCheck) return;
    
    // Block or capture the checking piece
    const checkerSquare = this.bitScanForward(checkers);
    const checkerPiece = this.getPieceAt(checkerSquare, them);
    const checkerMask = this.getEvasionMask(kingSquare, checkerSquare, checkerPiece);
    
    // Generate blocking moves or captures of checking piece
    this.generateBlockingMoves(moves, checkerMask, pinnedPieces);
  }

  generateQuietMoves(moves, kingSquare, pinnedPieces) {
    const us = this.side;
    
    // Pawn pushes
    this.generatePawnPushes(moves, kingSquare, pinnedPieces);
    
    // Knight moves
    this.generatePieceMoves(
      moves, 
      this.PIECE_TYPES.KNIGHT, 
      this.knightAttacks, 
      kingSquare, 
      pinnedPieces,
      false
    );
    
    // Bishop moves
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.BISHOP,
      kingSquare,
      pinnedPieces,
      false
    );
    
    // Rook moves
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.ROOK,
      kingSquare,
      pinnedPieces,
      false
    );
    
    // Queen moves
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.QUEEN,
      kingSquare,
      pinnedPieces,
      false
    );
    
    // King moves (non-captures)
    this.generateKingMoves(moves, kingSquare, false);
    
    // Castling
    this.generateCastling(moves, kingSquare);
  }

  generateCaptures(moves, kingSquare, pinnedPieces) {
    const us = this.side;
    const them = us ^ 1;
    
    // Pawn captures
    this.generatePawnCaptures(moves, kingSquare, pinnedPieces);
    
    // Knight captures
    this.generatePieceMoves(
      moves, 
      this.PIECE_TYPES.KNIGHT, 
      this.knightAttacks, 
      kingSquare, 
      pinnedPieces,
      true
    );
    
    // Bishop captures
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.BISHOP,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // Rook captures
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.ROOK,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // Queen captures
    this.generateSliderMoves(
      moves,
      this.PIECE_TYPES.QUEEN,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // King captures
    this.generateKingMoves(moves, kingSquare, true);
  }

  generateSpecialMoves(moves, kingSquare, pinnedPieces) {
    // En passant
    if (this.epSquare >= 0) {
      this.generateEnPassant(moves, kingSquare, pinnedPieces);
    }
  }

  generatePawnPushes(moves, kingSquare, pinnedPieces) {
    const us = this.side;
    const them = us ^ 1;
    const pawns = this.bitboards[us * 6 + this.PIECE_TYPES.PAWN - 1];
    const empty = ~this.occupancy[2];
    const promotionRank = us === this.COLORS.WHITE ? 7 : 0;
    
    let pawnBB = pawns;
    while (pawnBB) {
      const from = this.bitScanForward(pawnBB);
      pawnBB &= pawnBB - 1n;
      
      // Check if pawn is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      if (isPinned) continue;
      
      const push1 = from + (us === this.COLORS.WHITE ? 8 : -8);
      if (empty & (1n << BigInt(push1))) {
        // Single push
        if (Math.floor(push1 / 8) === promotionRank) {
          this.addPromotions(moves, from, push1, this.PIECE_TYPES.PAWN, 0);
        } else {
          this.addMove(moves, from, push1, this.PIECE_TYPES.PAWN, 0);
          
          // Double push
          const rank = Math.floor(from / 8);
          const push2 = from + (us === this.COLORS.WHITE ? 16 : -16);
          if ((us === this.COLORS.WHITE && rank === 1) || 
              (us === this.COLORS.BLACK && rank === 6)) {
            if (empty & (1n << BigInt(push2))) {
              this.addMove(moves, from, push2, this.PIECE_TYPES.PAWN, 0);
            }
          }
        }
      }
    }
  }

  generatePawnCaptures(moves, kingSquare, pinnedPieces) {
    const us = this.side;
    const them = us ^ 1;
    const pawns = this.bitboards[us * 6 + this.PIECE_TYPES.PAWN - 1];
    const enemyPieces = this.occupancy[them];
    const promotionRank = us === this.COLORS.WHITE ? 7 : 0;
    
    let pawnBB = pawns;
    while (pawnBB) {
      const from = this.bitScanForward(pawnBB);
      pawnBB &= pawnBB - 1n;
      
      // Check if pawn is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      
      // Generate captures
      const attacks = this.pawnAttacks[us][from] & enemyPieces;
      let attackBB = attacks;
      while (attackBB) {
        const to = this.bitScanForward(attackBB);
        attackBB &= attackBB - 1n;
        
        // Check if capture is legal for pinned pawn
        if (isPinned && !this.isMoveAlongPinRay(from, to, kingSquare)) {
          continue;
        }
        
        const captured = this.getPieceAt(to, them);
        if (Math.floor(to / 8) === promotionRank) {
          this.addPromotions(moves, from, to, this.PIECE_TYPES.PAWN, captured);
        } else {
          this.addMove(moves, from, to, this.PIECE_TYPES.PAWN, captured);
        }
      }
    }
  }

  generateEnPassant(moves, kingSquare, pinnedPieces) {
    const us = this.side;
    const them = us ^ 1;
    const epSquare = this.epSquare;
    const pawns = this.bitboards[us * 6 + this.PIECE_TYPES.PAWN - 1];
    
    // Get pawns that can capture en passant
    const attackers = pawns & this.pawnAttacks[them][epSquare];
    let attackerBB = attackers;
    
    while (attackerBB) {
      const from = this.bitScanForward(attackerBB);
      attackerBB &= attackerBB - 1n;
      
      // Check if pawn is pinned
      if (pinnedPieces & (1n << BigInt(from))) {
        // Special check for en passant pins
        if (!this.isEnPassantLegal(from, epSquare, kingSquare, us)) {
          continue;
        }
      }
      
      this.addMove(moves, from, epSquare, this.PIECE_TYPES.PAWN, 
                  this.PIECE_TYPES.PAWN, this.MOVE_FLAGS.ENPASSANT);
    }
  }

  generatePieceMoves(moves, pieceType, moveTable, kingSquare, pinnedPieces, capturesOnly) {
    const us = this.side;
    const them = us ^ 1;
    const pieces = this.bitboards[us * 6 + pieceType - 1];
    const targets = capturesOnly ? this.occupancy[them] : ~this.occupancy[us];
    
    let pieceBB = pieces;
    while (pieceBB) {
      const from = this.bitScanForward(pieceBB);
      pieceBB &= pieceBB - 1n;
      
      // Check if piece is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      
      // Get possible moves
      let movesBB = moveTable[from] & targets;
      
      // For pinned pieces, only allow moves along the pin ray
      if (isPinned) {
        movesBB &= this.getPinRay(from, kingSquare);
      }
      
      // Generate moves
      while (movesBB) {
        const to = this.bitScanForward(movesBB);
        movesBB &= movesBB - 1n;
        
        const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
        this.addMove(moves, from, to, pieceType, captured);
      }
    }
  }

  generateSliderMoves(moves, pieceType, kingSquare, pinnedPieces, capturesOnly) {
    const us = this.side;
    const them = us ^ 1;
    const pieces = this.bitboards[us * 6 + pieceType - 1];
    const targets = capturesOnly ? this.occupancy[them] : ~this.occupancy[us];
    
    let pieceBB = pieces;
    while (pieceBB) {
      const from = this.bitScanForward(pieceBB);
      pieceBB &= pieceBB - 1n;
      
      // Check if piece is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      
      // Get attack mask
      let attacks = this.getSliderAttacks(pieceType, from);
      attacks &= targets;
      
      // For pinned pieces, only allow moves along the pin ray
      if (isPinned) {
        attacks &= this.getPinRay(from, kingSquare);
      }
      
      // Generate moves
      while (attacks) {
        const to = this.bitScanForward(attacks);
        attacks &= attacks - 1n;
        
        const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
        this.addMove(moves, from, to, pieceType, captured);
      }
    }
  }

  generateKingMoves(moves, fromSquare, capturesOnly) {
    const us = this.side;
    const them = us ^ 1;
    const targets = capturesOnly ? this.occupancy[them] : ~this.occupancy[us];
    
    // Normal king moves
    let movesBB = this.kingAttacks[fromSquare] & targets;
    while (movesBB) {
      const to = this.bitScanForward(movesBB);
      movesBB &= movesBB - 1n;
      
      // Make sure destination is not attacked
      if (this.isSquareAttacked(to, them)) continue;
      
      const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
      this.addMove(moves, fromSquare, to, this.PIECE_TYPES.KING, captured);
    }
  }

  generateCastling(moves, kingSquare) {
    const us = this.side;
    const them = us ^ 1;
    
    if (this.isInCheck()) return;
    
    const castlingRights = this.castling;
    if (!castlingRights) return;
    
    // Generate kingside castling
    if (castlingRights & (us === this.COLORS.WHITE ? 0b0001 : 0b0100)) {
      this.generateCastle(moves, kingSquare, true, us, them);
    }
    
    // Generate queenside castling
    if (castlingRights & (us === this.COLORS.WHITE ? 0b0010 : 0b1000)) {
      this.generateCastle(moves, kingSquare, false, us, them);
    }
  }

  generateCastle(moves, kingSquare, kingside, us, them) {
    const [rookFrom, rookTo, kingTo, emptySquares, safeSquares] = 
      this.getCastleSquares(kingSquare, kingside, us);
    
    // Check if squares are empty and not attacked
    if ((this.occupancy[2] & emptySquares) !== 0n) return;
    if (this.areSquaresAttacked(safeSquares, them)) return;
    
    this.addMove(
      moves, 
      kingSquare, 
      kingTo, 
      this.PIECE_TYPES.KING, 
      0, 
      this.MOVE_FLAGS.CASTLING,
      rookFrom,
      rookTo
    );
  }

  // ===================== MOVE HELPERS =====================
  addMove(moves, from, to, piece, captured, flags = 0, extra1 = 0, extra2 = 0) {
    moves.push({
      from,
      to,
      piece,
      captured,
      promotion: 0,
      flags,
      extra1,
      extra2,
      score: 0
    });
  }

  addPromotions(moves, from, to, piece, captured) {
    for (const promo of [
      this.PIECE_TYPES.QUEEN,
      this.PIECE_TYPES.ROOK,
      this.PIECE_TYPES.BISHOP,
      this.PIECE_TYPES.KNIGHT
    ]) {
      this.addMove(
        moves, 
        from, 
        to, 
        piece, 
        captured, 
        this.MOVE_FLAGS.PROMOTION,
        promo
      );
    }
  }

  getPieceAt(square, color) {
    for (let type = 1; type <= 6; type++) {
      if (this.bitboards[color * 6 + type - 1] & (1n << BigInt(square))) {
        return type;
      }
    }
    return 0;
  }

  getSliderAttacks(pieceType, square) {
    const occupancy = this.occupancy[2];
    
    if (pieceType === this.PIECE_TYPES.BISHOP) {
      const mask = this.getBishopMask(square);
      const magic = this.bishopMagics[square];
      const index = Number(((occupancy & mask) * magic) >> 55n);
      return this.bishopAttacks[square][index];
    } else if (pieceType === this.PIECE_TYPES.ROOK) {
      const mask = this.getRookMask(square);
      const magic = this.rookMagics[square];
      const index = Number(((occupancy & mask) * magic) >> 52n);
      return this.rookAttacks[square][index];
    } else if (pieceType === this.PIECE_TYPES.QUEEN) {
      return this.getSliderAttacks(this.PIECE_TYPES.BISHOP, square) | 
             this.getSliderAttacks(this.PIECE_TYPES.ROOK, square);
    }
    
    return 0n;
  }

  isSquareAttacked(square, byColor) {
    // Pawns
    if (this.pawnAttacks[byColor ^ 1][square] & this.bitboards[byColor * 6 + this.PIECE_TYPES.PAWN - 1]) {
      return true;
    }
    
    // Knights
    if (this.knightAttacks[square] & this.bitboards[byColor * 6 + this.PIECE_TYPES.KNIGHT - 1]) {
      return true;
    }
    
    // King
    if (this.kingAttacks[square] & this.bitboards[byColor * 6 + this.PIECE_TYPES.KING - 1]) {
      return true;
    }
    
    // Sliding pieces
    const queens = this.bitboards[byColor * 6 + this.PIECE_TYPES.QUEEN - 1];
    const rooks = queens | this.bitboards[byColor * 6 + this.PIECE_TYPES.ROOK - 1];
    const bishops = queens | this.bitboards[byColor * 6 + this.PIECE_TYPES.BISHOP - 1];
    
    // Rooks/Queens
    if (this.getSliderAttacks(this.PIECE_TYPES.ROOK, square) & rooks) {
      return true;
    }
    
    // Bishops/Queens
    if (this.getSliderAttacks(this.PIECE_TYPES.BISHOP, square) & bishops) {
      return true;
    }
    
    return false;
  }

  areSquaresAttacked(squares, byColor) {
    let bb = squares;
    while (bb) {
      const sq = this.bitScanForward(bb);
      bb &= bb - 1n;
      
      if (this.isSquareAttacked(sq, byColor)) {
        return true;
      }
    }
    return false;
  }

  getEvasionMask(kingSquare, checkerSquare, checkerPiece) {
    if (checkerPiece === this.PIECE_TYPES.KNIGHT || 
        checkerPiece === this.PIECE_TYPES.PAWN) {
      return 1n << BigInt(checkerSquare);
    }
    
    // For sliding pieces, get the ray between king and checker
    let mask = 0n;
    const kingFile = kingSquare % 8;
    const kingRank = Math.floor(kingSquare / 8);
    const checkerFile = checkerSquare % 8;
    const checkerRank = Math.floor(checkerSquare / 8);
    
    const fileStep = Math.sign(checkerFile - kingFile);
    const rankStep = Math.sign(checkerRank - kingRank);
    
    let file = kingFile + fileStep;
    let rank = kingRank + rankStep;
    
    while (file !== checkerFile || rank !== checkerRank) {
      mask |= 1n << BigInt(rank * 8 + file);
      file += fileStep;
      rank += rankStep;
    }
    
    mask |= 1n << BigInt(checkerSquare);
    return mask;
  }

  getPinRay(from, kingSquare) {
    const kingFile = kingSquare % 8;
    const kingRank = Math.floor(kingSquare / 8);
    const fromFile = from % 8;
    const fromRank = Math.floor(from / 8);
    
    // Not on same line
    if (kingFile !== fromFile && kingRank !== fromRank && 
        Math.abs(kingFile - fromFile) !== Math.abs(kingRank - fromRank)) {
      return 0n;
    }
    
    let mask = 0n;
    const fileStep = Math.sign(fromFile - kingFile);
    const rankStep = Math.sign(fromRank - kingRank);
    
    let file = kingFile + fileStep;
    let rank = kingRank + rankStep;
    
    while (file >= 0 && file < 8 && rank >= 0 && rank < 8) {
      const sq = rank * 8 + file;
      mask |= 1n << BigInt(sq);
      
      if (sq === from) break;
      
      file += fileStep;
      rank += rankStep;
    }
    
    return mask;
  }

  isMoveAlongPinRay(from, to, kingSquare) {
    const ray = this.getPinRay(from, kingSquare);
    return (ray & (1n << BigInt(to))) !== 0n;
  }

  isEnPassantLegal(from, epSquare, kingSquare, color) {
    // After ep capture, check if king would be in check
    const capturedPawnSquare = epSquare + (color === this.COLORS.WHITE ? -8 : 8);
    const newOccupancy = this.occupancy[2] ^ 
                        (1n << BigInt(from)) ^ 
                        (1n << BigInt(epSquare)) ^ 
                        (1n << BigInt(capturedPawnSquare));
    
    // Check if king is attacked on the rank
    const kingRank = Math.floor(kingSquare / 8);
    const epRank = Math.floor(epSquare / 8);
    
    if (kingRank === epRank) {
      const fileStep = from < epSquare ? 1 : -1;
      let file = (from % 8) + fileStep;
      
      while (file >= 0 && file < 8) {
        const sq = kingRank * 8 + file;
        
        if (sq === epSquare || sq === from) {
          file += fileStep;
          continue;
        }
        
        if (newOccupancy & (1n << BigInt(sq))) {
          const piece = this.getPieceAt(sq, color ^ 1);
          if (piece === this.PIECE_TYPES.ROOK || piece === this.PIECE_TYPES.QUEEN) {
            return false;
          }
          break;
        }
        
        file += fileStep;
      }
    }
    
    return true;
  }

  getCastleSquares(kingSquare, kingside, color) {
    if (color === this.COLORS.WHITE) {
      if (kingside) {
        return [
          7, 5, 6, 0x60n, 0x70n // h1, f1, g1, f1g1, e1f1g1
        ];
      } else {
        return [
          0, 3, 2, 0xEn, 0x1Cn // a1, d1, c1, b1c1d1, c1d1e1
        ];
      }
    } else {
      if (kingside) {
        return [
          63, 61, 62, 0x6000000000000000n, 0x7000000000000000n // h8, f8, g8, f8g8, e8f8g8
        ];
      } else {
        return [
          56, 59, 58, 0xE00000000000000n, 0x1C00000000000000n // a8, d8, c8, b8c8d8, c8d8e8
        ];
      }
    }
  }

  // ===================== MOVE EXECUTION =====================
  makeMove(move) {
    const undo = {
      hash: this.hash,
      castling: this.castling,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock,
      captured: 0
    };
    
    const from = move.from;
    const to = move.to;
    const piece = move.piece;
    const color = this.side;
    const them = color ^ 1;
    
    // Update hash - remove moving piece from source square
    this.hash ^= this.zobrist.pieces[color * 6 + piece - 1][from];
    
    // Clear ep square in hash
    if (this.epSquare >= 0) {
      this.hash ^= this.zobrist.ep[this.epSquare];
    }
    
    // Handle captures
    if (move.flags === this.MOVE_FLAGS.CAPTURE || move.flags === this.MOVE_FLAGS.ENPASSANT) {
      let capturedSquare = to;
      let capturedPiece = move.captured;
      
      if (move.flags === this.MOVE_FLAGS.ENPASSANT) {
        capturedSquare = to + (color === this.COLORS.WHITE ? -8 : 8);
        capturedPiece = this.PIECE_TYPES.PAWN;
      }
      
      undo.captured = capturedPiece;
      
      // Remove captured piece from bitboards
      this.bitboards[them * 6 + capturedPiece - 1] ^= 1n << BigInt(capturedSquare);
      this.occupancy[them] ^= 1n << BigInt(capturedSquare);
      this.occupancy[2] ^= 1n << BigInt(capturedSquare);
      
      // Update hash - remove captured piece
      this.hash ^= this.zobrist.pieces[them * 6 + capturedPiece - 1][capturedSquare];
      
      // Reset halfmove clock
      this.halfmoveClock = 0;
    }
    
    // Move the piece
    this.bitboards[color * 6 + piece - 1] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[color] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[2] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    
    // Update hash - add moving piece to destination square
    this.hash ^= this.zobrist.pieces[color * 6 + piece - 1][to];
    
    // Handle promotions
    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
      const promo = move.promotion;
      
      // Remove pawn from destination
      this.bitboards[color * 6 + this.PIECE_TYPES.PAWN - 1] ^= 1n << BigInt(to);
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.PAWN - 1][to];
      
      // Add promoted piece
      this.bitboards[color * 6 + promo - 1] ^= 1n << BigInt(to);
      this.hash ^= this.zobrist.pieces[color * 6 + promo - 1][to];
    }
    
    // Handle castling
    if (move.flags === this.MOVE_FLAGS.CASTLING) {
      const rookFrom = move.extra1;
      const rookTo = move.extra2;
      
      // Move the rook
      this.bitboards[color * 6 + this.PIECE_TYPES.ROOK - 1] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[color] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[2] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      
      // Update hash for rook move
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookFrom];
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookTo];
    }
    
    // Update castling rights
    const castlingUpdate = this.getCastlingUpdate(from, to, piece, color);
    if (castlingUpdate) {
      this.hash ^= this.zobrist.castling[this.castling];
      this.castling &= ~castlingUpdate;
      this.hash ^= this.zobrist.castling[this.castling];
      undo.castling = this.castling | castlingUpdate; // Store original value
    }
    
    // Set en passant square
    this.epSquare = -1;
    if (piece === this.PIECE_TYPES.PAWN && Math.abs(to - from) === 16) {
      this.epSquare = from + (color === this.COLORS.WHITE ? 8 : -8);
      this.hash ^= this.zobrist.ep[this.epSquare];
    }
    
    // Update halfmove clock
    if (piece === this.PIECE_TYPES.PAWN || move.flags === this.MOVE_FLAGS.CAPTURE) {
      this.halfmoveClock = 0;
    } else {
      this.halfmoveClock++;
    }
    
    // Update fullmove number after black move
    if (color === this.COLORS.BLACK) {
      this.fullmoveNumber++;
    }
    
    // Switch side
    this.side = them;
    this.hash ^= this.zobrist.side;
    
    // Push to stack
    this.stack.push({
      move,
      hash: this.hash,
      castling: this.castling,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock,
      fullmoveNumber: this.fullmoveNumber,
      captured: undo.captured
    });
    
    return undo;
  }

  undoMove(move, undo) {
    const from = move.from;
    const to = move.to;
    const piece = move.piece;
    const color = this.side ^ 1; // Opposite of current side
    const them = color ^ 1;
    
    // Switch side first
    this.side = color;
    this.hash ^= this.zobrist.side;
    
    // Restore fullmove number
    if (color === this.COLORS.BLACK) {
      this.fullmoveNumber--;
    }
    
    // Restore castling rights
    if (this.castling !== undo.castling) {
      this.hash ^= this.zobrist.castling[this.castling];
      this.castling = undo.castling;
      this.hash ^= this.zobrist.castling[this.castling];
    }
    
    // Restore en passant
    if (this.epSquare !== undo.epSquare) {
      if (this.epSquare >= 0) this.hash ^= this.zobrist.ep[this.epSquare];
      this.epSquare = undo.epSquare;
      if (this.epSquare >= 0) this.hash ^= this.zobrist.ep[this.epSquare];
    }
    
    // Restore halfmove clock
    this.halfmoveClock = undo.halfmoveClock;
    
    // Move the piece back
    this.bitboards[color * 6 + piece - 1] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[color] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[2] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    
    // Handle promotions
    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
      const promo = move.promotion;
      
      // Remove promoted piece
      this.bitboards[color * 6 + promo - 1] ^= 1n << BigInt(to);
      
      // Add back pawn
      this.bitboards[color * 6 + this.PIECE_TYPES.PAWN - 1] ^= 1n << BigInt(to));
    }
    
    // Handle castling
    if (move.flags === this.MOVE_FLAGS.CASTLING) {
      const rookFrom = move.extra1;
      const rookTo = move.extra2;
      
      // Move the rook back
      this.bitboards[color * 6 + this.PIECE_TYPES.ROOK - 1] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[color] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[2] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
    }
    
    // Handle captures
    if (move.flags === this.MOVE_FLAGS.CAPTURE || move.flags === this.MOVE_FLAGS.ENPASSANT) {
      let capturedSquare = to;
      
      if (move.flags === this.MOVE_FLAGS.ENPASSANT) {
        capturedSquare = to + (color === this.COLORS.WHITE ? -8 : 8);
      }
      
      // Add back captured piece
      this.bitboards[them * 6 + undo.captured - 1] ^= 1n << BigInt(capturedSquare);
      this.occupancy[them] ^= 1n << BigInt(capturedSquare);
          // Move the piece back
    this.bitboards[color * 6 + piece - 1] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[color] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[2] ^= (1n << BigInt(from)) | (1n << BigInt(to));

    // Update hash - add moving piece back to source square
    this.hash ^= this.zobrist.pieces[color * 6 + piece - 1][from];
    this.hash ^= this.zobrist.pieces[color * 6 + piece - 1][to];

    // Handle promotions
    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
      const promo = move.promotion;
      
      // Remove promoted piece
      this.bitboards[color * 6 + promo - 1] ^= 1n << BigInt(to);
      this.hash ^= this.zobrist.pieces[color * 6 + promo - 1][to];
      
      // Add back pawn
      this.bitboards[color * 6 + this.PIECE_TYPES.PAWN - 1] ^= 1n << BigInt(to);
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.PAWN - 1][to];
    }
    
    // Handle castling
    if (move.flags === this.MOVE_FLAGS.CASTLING) {
      const rookFrom = move.extra1;
      const rookTo = move.extra2;
      
      // Move the rook back
      this.bitboards[color * 6 + this.PIECE_TYPES.ROOK - 1] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[color] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      this.occupancy[2] ^= (1n << BigInt(rookFrom)) | (1n << BigInt(rookTo));
      
      // Update hash for rook move
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookFrom];
      this.hash ^= this.zobrist.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookTo];
    }
    
    // Handle captures
    if (move.flags === this.MOVE_FLAGS.CAPTURE || move.flags === this.MOVE_FLAGS.ENPASSANT) {
      let capturedSquare = to;
      let capturedPiece = undo.captured;
      
      if (move.flags === this.MOVE_FLAGS.ENPASSANT) {
        capturedSquare = to + (color === this.COLORS.WHITE ? -8 : 8);
        capturedPiece = this.PIECE_TYPES.PAWN;
      }
      
      // Add back captured piece
      this.bitboards[them * 6 + capturedPiece - 1] ^= 1n << BigInt(capturedSquare);
      this.occupancy[them] ^= 1n << BigInt(capturedSquare);
      this.occupancy[2] ^= 1n << BigInt(capturedSquare);
      
      // Update hash - add captured piece back
      this.hash ^= this.zobrist.pieces[them * 6 + capturedPiece - 1][capturedSquare];
    }
    
    // Pop the stack
    this.stack.pop();
    this.ply--;
  }
      
      
      
   /////////////////////////   
   class Search {
    constructor(engine) {
        this.engine = engine;
        this.extensions = new SearchExtensions(engine);
        this.moveOrdering = new MoveOrdering(engine);
        this.probCut = new ProbCut(engine);
        this.timeManager = new TimeManager(engine);
        
        // Search state
        this.nodes = 0;
        this.seldepth = 0;
        this.stopSearch = false;
        this.pvTable = Array(engine.MAX_DEPTH).fill().map(() => []);
        
        // Statistics
        this.cutoffs = {
            nullMove: 0,
            probCut: 0,
            futility: 0,
            lmr: 0,
            history: 0
        };
    }

    async getBestMove(options = {}) {
        this.timeManager.init(options);
        this.resetSearchState();
        
        // Check for immediate draws
        if (this.engine.isDrawn()) {
            return this.engine.MOVE_NONE;
        }

        // Probe opening book
        const bookMove = this.engine.openingBook.getMove(this.engine.getFEN());
        if (bookMove) return bookMove;

        // Check tablebases
        const tbMove = this.engine.syzygy.probe(this.engine);
        if (tbMove) return tbMove;

        // Main search loop
        let bestMove = null;
        let bestScore = -this.engine.INFINITY;
        let aspirationWindow = 25; // Initial window size

        for (let depth = 1; depth <= this.engine.MAX_DEPTH; depth++) {
            let alpha = Math.max(-this.engine.INFINITY, bestScore - aspirationWindow);
            let beta = Math.min(this.engine.INFINITY, bestScore + aspirationWindow);

            while (true) {
                const score = await this.search(depth, alpha, beta, false, true);

                // Adjust aspiration window
                if (score <= alpha) {
                    alpha = Math.max(-this.engine.INFINITY, alpha - aspirationWindow);
                    beta = (alpha + beta) / 2;
                    aspirationWindow *= 2;
                } else if (score >= beta) {
                    beta = Math.min(this.engine.INFINITY, beta + aspirationWindow);
                    aspirationWindow *= 2;
                } else {
                    bestScore = score;
                    break;
                }

                // Check time after each iteration
                if (this.timeManager.shouldStop(this.nodes, depth)) {
                    break;
                }
            }

            // Early exit conditions
            if (this.stopSearch || 
                Math.abs(bestScore) >= this.engine.MATE_SCORE ||
                this.timeManager.shouldStop(this.nodes, depth)) {
                break;
            }

            aspirationWindow = Math.min(50, aspirationWindow * 1.5);
        }

        return bestMove || this.engine.generateMoves()[0];
    }

    async search(depth, alpha, beta, cutNode, isPvNode) {
        // Check termination conditions
        if (this.stopSearch) return alpha;
        if (this.engine.isDrawn()) return this.engine.getDynamicContempt();
        
        // QSearch at leaf nodes
        if (depth <= 0) {
            return this.qSearch(alpha, beta);
        }

        // TT probe
        const ttEntry = this.engine.probeTT();
        const ttMove = ttEntry?.move || null;
        const ttScore = ttEntry?.score || -this.engine.INFINITY;

        // TT cutoff
        if (!isPvNode && ttEntry && ttEntry.depth >= depth) {
            if (ttEntry.flag === 0) return ttScore;
            if (ttEntry.flag === 1 && ttScore >= beta) return beta;
            if (ttEntry.flag === 2 && ttScore <= alpha) return alpha;
        }

        // Check extension
        const inCheck = this.engine.isInCheck();
        const extension = this.extensions.getExtension(depth, ttMove, inCheck);
        depth += extension;

        // Razoring
        if (!isPvNode && !inCheck && depth <= 3) {
            const eval = this.engine.evaluate();
            if (eval + 125 * depth <= alpha) {
                return this.qSearch(alpha, beta);
            }
        }

        // Null move pruning
        if (!isPvNode && !inCheck && depth >= 2 && this.engine.hasNonPawns()) {
            const R = 3 + Math.min(3, depth / 6);
            
            this.engine.makeNullMove();
            const nullScore = -await this.search(depth - R, -beta, -beta + 1, true);
            this.engine.undoNullMove();

            if (nullScore >= beta) {
                this.cutoffs.nullMove++;
                return beta;
            }
        }

        // ProbCut
        if (!isPvNode && depth >= 4 && Math.abs(alpha - beta) === 1) {
            const probCutScore = await this.probCut.probe(depth, beta);
            if (probCutScore !== null && probCutScore >= beta) {
                this.cutoffs.probCut++;
                return beta;
            }
        }

        // Internal iterative deepening
        if (isPvNode && depth >= 6 && !ttMove) {
            await this.search(depth - 4, alpha, beta, false, true);
        }

        // Generate and order moves
        const moves = this.engine.generateMoves();
        if (moves.length === 0) {
            return inCheck ? -this.engine.MATE_VALUE + this.engine.ply : this.engine.getDynamicContempt();
        }

        this.moveOrdering.orderMoves(moves, ttMove, depth, isPvNode);

        // Main search loop
        let bestScore = -this.engine.INFINITY;
        let bestMove = moves[0];
        let legalMoves = 0;
        const improving = !inCheck && this.engine.evaluate() > 
            (this.engine.stack.length >= 2 ? this.engine.stack[this.engine.stack.length - 2].staticEval : -this.engine.INFINITY);

        for (let i = 0; i < moves.length; i++) {
            const move = moves[i];

            // Futility pruning
            if (!isPvNode && !inCheck && depth <= 7 && !move.captured && !move.promotion) {
                const margin = 150 + 175 * depth;
                if (this.engine.evaluate() + margin <= alpha) {
                    this.cutoffs.futility++;
                    continue;
                }
            }

            // Late move pruning
            if (!isPvNode && !inCheck && depth <= 8 && legalMoves >= this.moveOrdering.lmpTable[depth][improving ? 1 : 0]) {
                continue;
            }

            // Make move and search
            const undo = this.engine.makeMove(move);
            let score;

            // LMR - Late Move Reductions
            let reduction = this.moveOrdering.getReduction(depth, legalMoves, improving, move);
            if (reduction > 0) {
                score = -await this.search(depth - 1 - reduction, -beta, -alpha, true, false);
                if (score > alpha) {
                    score = -await this.search(depth - 1, -beta, -alpha, false, false);
                }
            } else {
                score = -await this.search(depth - 1, -beta, -alpha, false, false);
            }

            this.engine.undoMove(move, undo);

            // Beta cutoff
            if (score >= beta) {
                this.moveOrdering.updateHistory(move, depth, beta - alpha);

                if (!move.captured && !move.promotion) {
                    this.engine.updateKillers(move);
                }

                this.engine.storeTT(depth, beta, 1, move, isPvNode);
                return beta;
            }

            // Update best score
            if (score > bestScore) {
                bestScore = score;
                bestMove = move;
                if (score > alpha) {
                    alpha = score;
                }
            }

            legalMoves++;
        }

        // Store results in TT
        const flag = bestScore > alpha ? 0 : 2;
        this.engine.storeTT(depth, bestScore, flag, bestMove, isPvNode);

        return bestScore;
    }

    qSearch(alpha, beta) {
        const standPat = this.engine.evaluate();
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        // Delta pruning
        const deltaMargin = 75 + 150 * (this.engine.gamePhase() / 256);
        if (standPat + deltaMargin < alpha) {
            return alpha;
        }

        // Generate captures
        const moves = this.engine.generateMoves().filter(move => {
            return move.captured || 
                  (move.flags === this.engine.MOVE_FLAGS.PROMOTION && this.engine.see(move, -50));
        });

        // Sort moves using SEE
        moves.sort((a, b) => {
            const aValue = this.engine.see(a, 0) + (a.captured ? this.engine.pieceValue(a.captured) * 10 : 0);
            const bValue = this.engine.see(b, 0) + (b.captured ? this.engine.pieceValue(b.captured) * 10 : 0);
            return bValue - aValue;
        });

        // Search captures
        for (const move of moves) {
            // SEE pruning
            if (this.engine.see(move, -25 - Math.abs(standPat - alpha)) {
                continue;
            }

            const undo = this.engine.makeMove(move);
            const score = -this.qSearch(-beta, -alpha);
            this.engine.undoMove(move, undo);

            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }

        return alpha;
    }

    resetSearchState() {
        this.nodes = 0;
        this.seldepth = 0;
        this.stopSearch = false;
        this.cutoffs = {
            nullMove: 0,
            probCut: 0,
            futility: 0,
            lmr: 0,
            history: 0
        };
    }
}
//////////
// search-extensions.js
class SearchExtensions {
    constructor(engine) {
        this.engine = engine;
        this.MAX_EXTENSIONS = 2;
        this.SINGULAR_EXTENSION_DEPTH = 8;
        this.SINGULAR_MARGIN = 85;
    }

    getExtension(depth, ttMove, inCheck) {
        let extension = 0;

        // 1. Check extension (always extend checks)
        if (inCheck) {
            extension = 1;
        }
        
        // 2. Singular extension
        if (depth >= this.SINGULAR_EXTENSION_DEPTH && 
            ttMove && 
            !extension &&
            this.isSingularMove(ttMove, depth)) {
            extension = 1;
        }

        // 3. Passed pawn push extension
        if (!extension && this.isPassedPawnPush(ttMove)) {
            extension = 1;
        }

        // 4. Recapture extension
        if (!extension && this.isRecapture(ttMove)) {
            extension = 1;
        }

        return Math.min(this.MAX_EXTENSIONS, extension);
    }

    isSingularMove(move, depth) {
        // Skip if not deep enough or no TT entry
        if (depth < this.SINGULAR_EXTENSION_DEPTH) return false;
        
        const ttEntry = this.engine.probeTT();
        if (!ttEntry || ttEntry.depth < depth - 3) return false;

        // Singular beta margin
        const singularBeta = ttEntry.score - this.SINGULAR_MARGIN * depth / 8;
        
        // Multi-phase verification:
        
        // Phase 1: Null move verification
        this.engine.makeNullMove();
        const nullScore = -this.engine.search(
            Math.floor(depth / 2), 
            -singularBeta, 
            -singularBeta + 1, 
            true
        );
        this.engine.undoNullMove();
        
        if (nullScore >= singularBeta) return true;

        // Phase 2: Static exchange evaluation
        if (move.captured && this.engine.see(move) < 0) {
            return false;
        }

        // Phase 3: Full verification search
        const undo = this.engine.makeMove(move);
        const score = -this.engine.search(
            depth - 3,
            -singularBeta,
            -singularBeta + 1,
            true
        );
        this.engine.undoMove(move, undo);

        return score < singularBeta;
    }

    isPassedPawnPush(move) {
        if (!move || move.piece !== this.engine.PIECE_TYPES.PAWN) return false;
        
        const to = move.to;
        const color = this.engine.side;
        const rank = Math.floor(to / 8);
        
        // Check if it's a passed pawn push
        if (color === this.engine.COLORS.WHITE) {
            return rank >= 4 && 
                   !(this.engine.bitboards[this.engine.COLORS.BLACK * 6 + this.engine.PIECE_TYPES.PAWN - 1] & 
                     this.engine.passedPawnMasks[this.engine.COLORS.WHITE][to]);
        } else {
            return rank <= 3 && 
                   !(this.engine.bitboards[this.engine.COLORS.WHITE * 6 + this.engine.PIECE_TYPES.PAWN - 1] & 
                     this.engine.passedPawnMasks[this.engine.COLORS.BLACK][to]);
        }
    }

    isRecapture(move) {
        if (!move || !move.captured) return false;
        
        // Check if this is recapturing the opponent's last moved piece
        if (this.engine.stack.length < 1) return false;
        
        const lastMove = this.engine.stack[this.engine.stack.length - 1].move;
        return lastMove && move.to === lastMove.to;
    }

    shouldPrune(move, depth, improving) {
        // 1. Futility pruning conditions
        if (!this.engine.isInCheck() && 
            depth <= 7 && 
            !move.captured && 
            !move.promotion) {
            
            const margin = 150 + 175 * depth - (improving ? 50 : 0);
            if (this.engine.evaluate() + margin <= this.engine.alpha) {
                return true;
            }
        }

        // 2. History pruning
        if (depth <= 4 && 
            !move.captured && 
            !move.promotion && 
            this.getHistoryScore(move) < depth * depth * 2) {
            return true;
        }

        // 3. SEE pruning for quiet moves
        if (depth <= 5 && 
            !move.captured && 
            !move.promotion && 
            this.engine.see(move, -50 * depth) < 0) {
            return true;
        }

        return false;
    }

    getHistoryScore(move) {
        const from = move.from;
        const to = move.to;
        const piece = move.piece;
        const color = this.engine.side;
        
        return this.engine.historyHeuristic[
            color * 49152 + // Color offset
            from * 768 +    // From square offset
            piece * 64 +    // Piece type offset
            to              // To square
        ];
    }

    getLmrReduction(depth, moveCount, improving, move) {
        let reduction = Math.floor(Math.log(depth) * Math.log(moveCount) / 1.8);
        
        // Adjust based on move characteristics
        if (!improving) reduction += 1;
        if (move.captured || move.promotion) reduction = 0;
        
        // History-based adjustment
        const history = this.getHistoryScore(move);
        if (history < 0) {
            reduction += Math.min(2, -history / 20000);
        }
        
        return Math.max(0, Math.min(depth - 1, reduction));
    }
}
//////////
// ===================== SINGULAR EXTENSIONS =====================
class SingularExtensionManager {
  constructor() {
    // Extension history table [depth][moveKey]
    this.extensionHistory = new Map();
    
    // Minimum depth for singular extensions
    this.minDepth = 8;
    
    // Maximum reduction for verification search
    this.maxReduction = 3;
    
    // Beta margin for singular checks
    this.betaMargin = 85;
    
    // Threshold for considering a move singular
    this.singularThreshold = 100;
    
    // Depth divisor for margin calculation
    this.depthDivisor = 8;
  }

  // Check if a move should be extended
  shouldExtend(position, move, depth, alpha, beta) {
    if (depth < this.minDepth) return false;
    if (position.isInCheck()) return false;
    if (move.captured || move.promotion) return false;
    
    // Check transposition table for previous results
    const tt = position.probeTT();
    if (!tt || tt.depth < depth - 3) return false;
    
    // Don't extend if this is the TT move
    if (tt.move && tt.move.from === move.from && tt.move.to === move.to) {
      return false;
    }
    
    // Calculate singular beta
    const singularBeta = Math.max(
      tt.score - this.betaMargin * Math.floor(depth / this.depthDivisor),
      -position.MATE_VALUE
    );
    
    // Null-move verification for faster pruning
    if (depth >= 10 && !position.isInCheck()) {
      position.makeNullMove();
      const nullScore = -position.search(
        Math.floor(depth / 2) - 1,
        -singularBeta,
        -singularBeta + 1,
        false
      );
      position.undoNullMove();
      
      if (nullScore >= singularBeta) {
        return false;
      }
    }
    
    // Perform verification search
    const undo = position.makeMove(move);
    const score = -position.search(
      depth - this.maxReduction - 1,
      -singularBeta,
      -singularBeta + 1,
      false
    );
    position.undoMove(move, undo);
    
    // Check if the move is singular (score drops significantly)
    const isSingular = score < singularBeta - this.singularThreshold;
    
    // Update extension history
    if (isSingular) {
      this.recordExtension(depth, move);
      return true;
    }
    
    return false;
  }

  // Record successful extensions in history
  recordExtension(depth, move) {
    const moveKey = this.getMoveKey(move);
    const depthKey = Math.min(depth, 20); // Cap depth for history
    
    if (!this.extensionHistory.has(depthKey)) {
      this.extensionHistory.set(depthKey, new Map());
    }
    
    const depthMap = this.extensionHistory.get(depthKey);
    depthMap.set(moveKey, (depthMap.get(moveKey) || 0) + 1);
  }

  // Check if a move has been frequently extended before
  hasHistoryOfExtensions(depth, move) {
    const moveKey = this.getMoveKey(move);
    const depthKey = Math.min(depth, 20);
    
    if (!this.extensionHistory.has(depthKey)) return false;
    
    const count = this.extensionHistory.get(depthKey).get(moveKey) || 0;
    return count > 2; // Only if extended multiple times before
  }

  // Create a unique key for a move
  getMoveKey(move) {
    return (move.from << 16) | (move.to << 8) | move.piece;
  }

  // Clear history between searches
  clearHistory() {
    this.extensionHistory.clear();
  }

  // Adjust beta margin based on game phase
  getDynamicBetaMargin(position, depth) {
    const phase = position.gamePhase() / 256;
    // Use larger margins in endgame where singular moves are more critical
    return this.betaMargin * (0.7 + phase * 0.6);
  }

  // Multi-phase singular check (optimized version)
  async multiPhaseSingularCheck(position, move, depth, alpha, beta) {
    // Phase 1: Quick null-move check
    const singularBeta = Math.max(
      position.probeTT().score - this.getDynamicBetaMargin(position, depth),
      -position.MATE_VALUE
    );
    
    if (depth >= 10) {
      position.makeNullMove();
      const nullScore = -await position.search(
        Math.floor(depth / 2) - 1,
        -singularBeta,
        -singularBeta + 1,
        false
      );
      position.undoNullMove();
      
      if (nullScore >= singularBeta) {
        return false;
      }
    }
    
    // Phase 2: Static exchange evaluation for captures
    if (move.captured && position.see(move) < 0) {
      return false;
    }
    
    // Phase 3: Full verification search
    const undo = position.makeMove(move);
    const score = -await position.search(
      depth - this.getReduction(depth) - 1,
      -singularBeta,
      -singularBeta + 1,
      false
    );
    position.undoMove(move, undo);
    
    return score < singularBeta - this.singularThreshold;
  }

  // Dynamic reduction based on depth and history
  getReduction(depth) {
    const baseReduction = this.maxReduction;
    // Increase reduction at higher depths
    return Math.min(baseReduction + Math.floor(depth / 6), 6);
  }
}



///////////
// move-ordering
class MoveOrdering {
    constructor(engine) {
        this.engine = engine;
        
        // History tables
        this.historyHeuristic = new Int32Array(12 * 64 * 12 * 64); // [piece][from][to]
        this.counterMoves = Array.from({length: 12}, () => new Array(64).fill(null));
        this.followupMoves = Array.from({length: 12}, () => new Array(64).fill(null));
        
        // Killer moves (2 per ply)
        this.killers = Array.from({length: 2}, () => new Array(engine.MAX_DEPTH).fill(null));
        
        // Butterfly board (for quiet moves)
        this.butterfly = new Int32Array(64 * 64);
        
        // LMP (Late Move Pruning) table [depth][improving]
        this.lmpTable = [
            [0, 0],    // depth 0
            [5, 5],    // depth 1
            [8, 10],   // depth 2
            [12, 15],  // depth 3
            [20, 25],  // depth 4
            [25, 30],  // depth 5
            [30, 40],  // depth 6
            [40, 50],  // depth 7
            [50, 60]   // depth 8+
        ];
        
        // Reduction lookup table [depth][moveNumber]
        this.reductionTable = Array(64).fill().map(() => new Array(64).fill(0));
        this.initReductionTable();
    }
    
    initReductionTable() {
        for (let depth = 1; depth < 64; depth++) {
            for (let moveNum = 1; moveNum < 64; moveNum++) {
                this.reductionTable[depth][moveNum] = 
                    Math.log(depth) * Math.log(moveNum) / 1.8;
            }
        }
    }

    orderMoves(moves, ttMove, depth, isPvNode) {
        for (const move of moves) {
            let score = 0;
            
            // 1. TT move gets highest priority
            if (ttMove && this.isSameMove(move, ttMove)) {
                score = 1000000;
            }
            // 2. Winning captures (SEE > 0)
            else if (move.captured && this.engine.see(move, 0)) {
                score = 90000 + this.captureValue(move);
            }
            // 3. Killer moves
            else if (this.isKiller(move, depth)) {
                score = 80000;
            }
            // 4. Counter moves
            else if (this.isCounterMove(move)) {
                score = 70000;
            }
            // 5. Follow-up moves
            else if (this.isFollowupMove(move)) {
                score = 60000;
            }
            // 6. History heuristic
            else {
                score = this.getHistoryScore(move);
            }
            
            // 7. Promotion bonus
            if (move.flags === this.engine.MOVE_FLAGS.PROMOTION) {
                score += 50000 + (move.promotion === this.engine.PIECE_TYPES.QUEEN ? 200 : 100);
            }
            
            // 8. Check bonus
            if (this.givesCheck(move)) {
                score += 30000;
            }
            
            // 9. Passed pawn push in endgame
            if (move.piece === this.engine.PIECE_TYPES.PAWN) {
                const phase = this.engine.gamePhase() / 256;
                if (phase > 0.6) { // Endgame
                    const rank = Math.floor(move.to / 8);
                    const promotionDist = this.engine.side === this.engine.COLORS.WHITE ? 7 - rank : rank;
                    score += (6 - promotionDist) * 20;
                }
            }
            
            // 10. PV node bonus
            if (isPvNode) {
                score += 1000;
            }
            
            move.score = score;
        }
        
        // Sort moves in descending order
        moves.sort((a, b) => b.score - a.score);
    }

    getReduction(depth, moveNumber, improving, move) {
        let reduction = this.reductionTable[Math.min(depth, 63)][Math.min(moveNumber, 63)];
        
        // Adjust based on move characteristics
        if (!improving) reduction += 1;
        if (move.captured || move.promotion) reduction = 0;
        
        // History-based adjustment
        const history = this.getHistoryScore(move);
        if (history < 0) {
            reduction += Math.min(2, -history / 20000);
        }
        
        return Math.max(0, Math.min(depth - 1, reduction));
    }

    updateHistory(move, depth, bonus, isCut) {
        const from = move.from;
        const to = move.to;
        const piece = move.piece;
        const color = this.engine.side;
        
        // Update history heuristic
        const historyIndex = color * 49152 + from * 768 + piece * 64 + to;
        const update = depth * depth * Math.min(10, bonus);
        
        if (isCut) {
            this.historyHeuristic[historyIndex] += update;
        } else {
            this.historyHeuristic[historyIndex] -= update;
        }
        
        // Keep history within bounds
        this.historyHeuristic[historyIndex] = Math.max(
            -2000000,
            Math.min(2000000, this.historyHeuristic[historyIndex])
        );
        
        // Update butterfly board
        this.butterfly[from * 64 + to] += depth * depth;
        
        // Update counter moves if previous move exists
        if (this.engine.stack.length > 0) {
            const prevMove = this.engine.stack[this.engine.stack.length - 1].move;
            if (prevMove) {
                this.counterMoves[prevMove.piece][prevMove.to] = move;
            }
        }
        
        // Update follow-up moves if previous previous move exists
        if (this.engine.stack.length > 1) {
            const prevPrevMove = this.engine.stack[this.engine.stack.length - 2].move;
            if (prevPrevMove) {
                this.followupMoves[prevPrevMove.piece][prevPrevMove.to] = move;
            }
        }
        
        // Update killer moves
        if (!move.captured && !move.promotion && isCut) {
            if (!this.isSameMove(move, this.killers[0][this.engine.ply])) {
                this.killers[1][this.engine.ply] = this.killers[0][this.engine.ply];
                this.killers[0][this.engine.ply] = move;
            }
        }
    }

    // Helper methods
    isSameMove(a, b) {
        return a && b && a.from === b.from && a.to === b.to && 
               (!a.promotion || a.promotion === b.promotion);
    }

    captureValue(move) {
        // MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        return this.engine.pieceValue(move.captured) * 10 - this.engine.pieceValue(move.piece);
    }

    isKiller(move, depth) {
        return (this.isSameMove(move, this.killers[0][depth]) || 
                this.isSameMove(move, this.killers[1][depth])) &&
               !move.captured && !move.promotion;
    }

    isCounterMove(move) {
        if (this.engine.stack.length === 0) return false;
        const prevMove = this.engine.stack[this.engine.stack.length - 1].move;
        return prevMove && this.isSameMove(move, this.counterMoves[prevMove.piece][prevMove.to]);
    }

    isFollowupMove(move) {
        if (this.engine.stack.length < 2) return false;
        const prevPrevMove = this.engine.stack[this.engine.stack.length - 2].move;
        return prevPrevMove && this.isSameMove(move, this.followupMoves[prevPrevMove.piece][prevPrevMove.to]);
    }

    getHistoryScore(move) {
        const from = move.from;
        const to = move.to;
        const piece = move.piece;
        const color = this.engine.side;
        return this.historyHeuristic[color * 49152 + from * 768 + piece * 64 + to];
    }

    givesCheck(move) {
        // Simplified check detection - in practice should use full check detection
        const pieceType = move.promotion || move.piece;
        if (pieceType === this.engine.PIECE_TYPES.KING) {
            return false; // King moves don't give check
        }
        
        const enemyKing = this.engine.bitboards[(this.engine.side ^ 1) * 6 + this.engine.PIECE_TYPES.KING - 1];
        if (!enemyKing) return false;
        
        const kingSquare = this.engine.bitScanForward(enemyKing);
        const attacks = this.engine.getAttacks(move.to, pieceType, this.engine.side);
        
        return (attacks & enemyKing) !== 0n;
    }
}
/////////
// search/parallel
class ParallelSearcher {
  constructor(engine, config = {}) {
    this.engine = engine;
    this.config = {
      threads: Math.max(1, navigator.hardwareConcurrency - 1),
      ttSizeMB: 64,
      minSplitDepth: 4,
      maxNodesPerThread: 5000000,
      ...config
    };

    this.workers = [];
    this.taskQueue = [];
    this.activeTasks = 0;
    this.globalStop = false;
    this.ttMutex = new SharedArrayBufferMutex();
    this.initSharedTT();
    this.initWorkers();
  }

  initSharedTT() {
    const ttSize = Math.floor((this.config.ttSizeMB * 1024 * 1024) / 16);
    this.sharedTT = new SharedArrayBuffer(ttSize * 16);
    this.ttView = new DataView(this.sharedTT);
    this.ttEntries = ttSize;
  }

  initWorkers() {
    if (typeof Worker === 'undefined') {
      console.warn('Web Workers not available, falling back to single-threaded');
      this.config.threads = 1;
      return;
    }

    const workerCode = `
      ${this.engine.toString()}
      ${ParallelSearchWorker.toString()}
      const worker = new ParallelSearchWorker();
      onmessage = (e) => worker.handleMessage(e.data);
    `;

    for (let i = 0; i < this.config.threads; i++) {
      const blob = new Blob([workerCode], { type: 'application/javascript' });
      const worker = new Worker(URL.createObjectURL(blob));
      
      worker.onmessage = (e) => this.handleWorkerResponse(e.data);
      worker.postMessage({
        type: 'init',
        threadId: i,
        sharedTT: this.sharedTT,
        config: this.config
      });

      this.workers.push(worker);
    }
  }

  async iterativeDeepening(position, options = {}) {
    this.globalStop = false;
    let bestMove = null;
    let bestScore = -this.engine.INFINITY;
    let lastBestMove = null;
    let stableCount = 0;

    for (let depth = 1; depth <= options.maxDepth || 64; depth++) {
      if (this.globalStop) break;

      const windowSize = this.getAspirationWindow(depth, bestScore);
      let alpha = bestScore - windowSize;
      let beta = bestScore + windowSize;

      // Lazy SMP - each worker searches independently with slightly different parameters
      const tasks = this.workers.map((worker, i) => {
        const taskId = performance.now() + i;
        const workerDepth = depth + (i % 3) - 1; // Vary depths slightly
        
        return new Promise((resolve) => {
          this.taskQueue.push({
            taskId,
            resolve,
            depth: workerDepth,
            alpha,
            beta
          });

          worker.postMessage({
            type: 'search',
            taskId,
            position: position.clone(),
            depth: workerDepth,
            alpha,
            beta,
            maxNodes: Math.floor(this.config.maxNodesPerThread / this.workers.length)
          });
        });
      });

      const results = await Promise.all(tasks);
      const bestResult = results.reduce((best, res) => 
        res.score > best.score ? res : best
      );

      // Check for stability
      if (bestResult.move && bestResult.move.san === lastBestMove?.san) {
        stableCount++;
      } else {
        stableCount = 0;
      }

      // Update best move if we have a significant improvement or new best move
      if (bestResult.score > bestScore + 50 || 
          (bestResult.move && bestResult.move.san !== lastBestMove?.san)) {
        bestScore = bestResult.score;
        bestMove = bestResult.move;
        lastBestMove = bestResult.move;
      }

      // Early exit conditions
      if (Math.abs(bestScore) >= this.engine.MATE_SCORE - depth) break;
      if (stableCount >= 3 && depth >= 12) break;
      if (options.timeManager?.shouldStop()) break;
    }

    return bestMove || position.generateMoves()[0];
  }

  getAspirationWindow(depth, lastScore) {
    if (depth <= 4) return this.engine.INFINITY;
    if (Math.abs(lastScore) >= this.engine.MATE_SCORE - 100) return this.engine.INFINITY;
    
    // Dynamic window sizing based on depth and previous score
    return Math.min(500, 25 + depth * 15);
  }

  handleWorkerResponse(response) {
    const task = this.taskQueue.find(t => t.taskId === response.taskId);
    if (!task) return;

    task.resolve(response);
    this.taskQueue = this.taskQueue.filter(t => t.taskId !== response.taskId);
  }

  stopSearch() {
    this.globalStop = true;
    this.workers.forEach(worker => worker.postMessage({ type: 'stop' }));
  }

  destroy() {
    this.workers.forEach(worker => worker.terminate());
    this.workers = [];
  }
}

class ParallelSearchWorker {
  constructor() {
    this.threadId = 0;
    this.tt = null;
    this.engine = null;
    this.currentSearchId = 0;
  }

  handleMessage(data) {
    switch(data.type) {
      case 'init':
        this.threadId = data.threadId;
        this.engine = new (eval(data.engine))();
        this.engine.initSharedTT(data.sharedTT);
        break;
        
      case 'search':
        this.currentSearchId = data.taskId;
        const result = this.search(
          data.position, 
          data.depth, 
          data.alpha, 
          data.beta,
          data.maxNodes
        );
        self.postMessage({
          type: 'result',
          taskId: data.taskId,
          ...result
        });
        break;
        
      case 'stop':
        this.engine.stopSearch = true;
        break;
    }
  }

  search(position, depth, alpha, beta, maxNodes) {
    this.engine.stopSearch = false;
    this.engine.nodes = 0;
    
    let bestScore = -this.engine.INFINITY;
    let bestMove = null;
    let pv = [];
    
    // Use a mix of ABDADA and YBWC parallel search techniques
    for (let d = 1; d <= depth && !this.engine.stopSearch; d++) {
      if (this.engine.nodes >= maxNodes) break;
      
      const score = this.engine.alphabeta(
        position, 
        d, 
        alpha, 
        beta, 
        true, 
        this.threadId,
        this.currentSearchId
      );
      
      if (this.engine.stopSearch) break;
      
      if (score > bestScore) {
        bestScore = score;
        bestMove = this.engine.getPVMove();
        pv = this.engine.getPV();
        
        if (score >= beta) break;
        if (score > alpha) alpha = score;
      }
    }
    
    return {
      score: bestScore,
      move: bestMove,
      pv,
      nodes: this.engine.nodes,
      depth
    };
  }
}

// utils/concurrency
class SharedArrayBufferMutex {
  constructor() {
    this.lock = new Int32Array(new SharedArrayBuffer(4));
  }

  acquire() {
    while (Atomics.compareExchange(this.lock, 0, 0, 1) !== 0) {
      Atomics.wait(this.lock, 0, 1);
    }
  }

  release() {
    Atomics.store(this.lock, 0, 0);
    Atomics.notify(this.lock, 0, 1);
  }

  withLock(fn) {
    this.acquire();
    try {
      return fn();
    } finally {
      this.release();
    }
  }
}
///////
class MCTSSearcher {
  constructor(engine, config = {}) {
    this.engine = engine;
    this.config = {
      iterations: 5000,           // Default number of iterations per move
      cpuct: 1.5,                 // Exploration constant
      dirichletAlpha: 0.3,        // Dirichlet noise alpha
      dirichletEpsilon: 0.25,     // Dirichlet noise weight
      fpuReduction: 0.2,          // First play urgency reduction
      virtualLoss: 3,             // Virtual loss for parallel searches
      batchSize: 8,               // Neural network batch size
      threads: 1,                 // Number of parallel search threads
      ...config
    };

    this.nodes = new Map();
    this.root = null;
    this.neuralNet = null;
    this.workers = [];
    this.initWorkers();
  }

  async initWorkers() {
    if (this.config.threads > 1 && typeof Worker !== 'undefined') {
      const workerCode = `
        ${this.engine.toString()}
        ${MCTSWorker.toString()}
        const worker = new MCTSWorker();
        onmessage = (e) => worker.handleMessage(e.data);
      `;

      for (let i = 0; i < this.config.threads; i++) {
        const blob = new Blob([workerCode], { type: 'application/javascript' });
        const worker = new Worker(URL.createObjectURL(blob));
        
        worker.onmessage = (e) => this.handleWorkerResponse(e.data);
        worker.postMessage({
          type: 'init',
          threadId: i,
          config: this.config
        });

        this.workers.push(worker);
      }
    }
  }

  async getBestMove(position, options = {}) {
    const startTime = Date.now();
    this.root = new MCTSNode(null, null, position.clone());
    this.nodes.clear();
    this.nodes.set(position.hash, this.root);

    // Pre-expand root with neural net predictions
    await this.expandNode(this.root);

    // Add Dirichlet noise for root exploration
    if (this.config.dirichletAlpha > 0) {
      this.addDirichletNoise(this.root);
    }

    let iterations = 0;
    const maxTime = options.timeBudget || 5000;

    while (iterations < this.config.iterations && 
           Date.now() - startTime < maxTime) {
      if (options.timeManager?.shouldStop()) break;

      if (this.workers.length > 0) {
        // Parallel search
        const tasks = this.workers.map(worker => {
          return new Promise(resolve => {
            worker.postMessage({
              type: 'search',
              nodeId: this.root.id,
              position: position.clone(),
              maxTime: maxTime - (Date.now() - startTime)
            });
          });
        });

        await Promise.all(tasks);
      } else {
        // Single-threaded search
        await this.searchIteration(this.root);
      }

      iterations++;
    }

    // Select best move
    const bestChild = this.selectBestChild(this.root, 0);
    return bestChild.move;
  }

  async searchIteration(node) {
    const path = [node];
    let current = node;

    // Selection
    while (current.isFullyExpanded() && !current.isTerminal()) {
      current = this.selectChild(current);
      path.push(current);
    }

    // Expansion
    if (!current.isTerminal()) {
      await this.expandNode(current);
      if (current.children.length > 0) {
        current = this.selectChild(current);
        path.push(current);
      }
    }

    // Simulation (with virtual loss for parallel searches)
    const value = await this.simulate(current);

    // Backpropagation
    for (const node of path) {
      node.update(value);
    }
  }

  async expandNode(node) {
    if (node.expanded) return;
    
    const moves = node.position.generateMoves();
    if (moves.length === 0) return;

    // Get neural network predictions
    const predictions = await this.getPredictions(node.position);

    // Create child nodes
    for (let i = 0; i < moves.length; i++) {
      const move = moves[i];
      const newPosition = node.position.clone();
      newPosition.makeMove(move);

      const childNode = new MCTSNode(node, move, newPosition);
      childNode.policy = predictions.policy[i];
      childNode.value = predictions.value;

      node.children.push(childNode);
      this.nodes.set(newPosition.hash, childNode);
    }

    node.expanded = true;
  }

  async getPredictions(position) {
    if (this.neuralNet) {
      // Use neural network for predictions
      return await this.neuralNet.predict(position);
    } else {
      // Fallback to uniform policy and engine evaluation
      const moves = position.generateMoves();
      const policy = Array(moves.length).fill(1 / moves.length);
      const value = this.engine.evaluate(position) / 100; // Scale to [-1, 1]
      
      return { policy, value };
    }
  }

  selectChild(node) {
    let bestScore = -Infinity;
    let bestChild = null;

    const totalVisits = Math.sqrt(node.visits);

    for (const child of node.children) {
      // UCT formula with neural network guidance
      const exploration = this.config.cpuct * 
        child.policy * 
        totalVisits / (1 + child.visits);

      // First play urgency reduction
      const exploitation = child.visits > 0 ? 
        child.value : 
        node.value - this.config.fpuReduction;

      const score = exploitation + exploration;

      if (score > bestScore) {
        bestScore = score;
        bestChild = child;
      }
    }

    return bestChild;
  }

  selectBestChild(node, temperature = 1) {
    if (temperature === 0) {
      // Select most visited
      return node.children.reduce((a, b) => 
        a.visits > b.visits ? a : b
      );
    } else {
      // Sample with temperature
      const visitCounts = node.children.map(c => Math.pow(c.visits, 1 / temperature));
      const sum = visitCounts.reduce((a, b) => a + b, 0);
      const probs = visitCounts.map(v => v / sum);
      
      let r = Math.random();
      for (let i = 0; i < node.children.length; i++) {
        r -= probs[i];
        if (r <= 0) return node.children[i];
      }
      return node.children[0];
    }
  }

  async simulate(node) {
    if (node.position.isGameOver()) {
      const result = node.position.getGameResult();
      return result === 0.5 ? 0 : (result === node.position.side ? 1 : -1);
    }

    // Short-circuit with quick evaluation in late game
    if (node.position.ply > 40) {
      return this.engine.evaluate(node.position) / 100;
    }

    // Use quick rollout policy
    let current = node.position.clone();
    let depth = 0;
    
    while (depth < 20 && !current.isGameOver()) {
      const moves = current.generateMoves();
      const move = this.selectRolloutMove(moves);
      current.makeMove(move);
      depth++;
    }

    const result = current.getGameResult();
    return result === 0.5 ? 0 : (result === node.position.side ? 1 : -1);
  }

  selectRolloutMove(moves) {
    // Simple heuristic-based rollout policy
    const captureMoves = moves.filter(m => m.flags & this.engine.FLAGS.CAPTURE);
    const checks = moves.filter(m => this.givesCheck(m));

    if (captureMoves.length > 0) {
      // Select highest value capture
      captureMoves.sort((a, b) => 
        this.engine.pieceValue(b.captured) - this.engine.pieceValue(a.captured)
      );
      return captureMoves[0];
    } else if (checks.length > 0) {
      // Select random check
      return checks[Math.floor(Math.random() * checks.length)];
    } else {
      // Select random move
      return moves[Math.floor(Math.random() * moves.length)];
    }
  }

  addDirichletNoise(node) {
    const dirichlet = new Array(node.children.length);
    let sum = 0;
    
    // Generate Dirichlet distributed noise
    for (let i = 0; i < node.children.length; i++) {
      dirichlet[i] = -Math.log(Math.random()); // Exponential distribution
      sum += dirichlet[i];
    }
    
    // Apply to child nodes
    for (let i = 0; i < node.children.length; i++) {
      node.children[i].policy = 
        (1 - this.config.dirichletEpsilon) * node.children[i].policy +
        this.config.dirichletEpsilon * (dirichlet[i] / sum);
    }
  }

  givesCheck(move) {
    // Fast check detection
    const undo = this.position.makeMove(move);
    const inCheck = this.position.isInCheck();
    this.position.undoMove(move, undo);
    return inCheck;
  }

  handleWorkerResponse(data) {
    // Handle responses from parallel workers
    if (data.type === 'result') {
      const node = this.nodes.get(data.nodeId);
      if (node) {
        node.update(data.value);
      }
    }
  }

  destroy() {
    this.workers.forEach(worker => worker.terminate());
    this.workers = [];
  }
}

class MCTSNode {
  constructor(parent, move, position) {
    this.id = position.hash;
    this.parent = parent;
    this.move = move;
    this.position = position;
    this.children = [];
    this.visits = 0;
    this.valueSum = 0;
    this.value = 0;
    this.policy = 0;
    this.expanded = false;
    this.virtualLoss = 0;
  }

  get isTerminal() {
    return this.position.isGameOver();
  }

  get isFullyExpanded() {
    return this.expanded && this.children.length > 0;
  }

  get valueEstimate() {
    return this.visits > 0 ? this.valueSum / this.visits : this.value;
  }

  update(value) {
    this.visits++;
    this.valueSum += value;
    this.virtualLoss = 0;
  }

  applyVirtualLoss() {
    this.virtualLoss += this.config.virtualLoss;
  }
}

class MCTSWorker {
  constructor() {
    this.threadId = 0;
    this.config = null;
    this.engine = null;
  }

  handleMessage(data) {
    switch(data.type) {
      case 'init':
        this.threadId = data.threadId;
        this.config = data.config;
        this.engine = new (eval(data.engine))();
        break;
        
      case 'search':
        this.search(data.nodeId, data.position, data.maxTime)
          .then(result => {
            self.postMessage({
              type: 'result',
              nodeId: data.nodeId,
              value: result
            });
          });
        break;
    }
  }

  async search(nodeId, position, maxTime) {
    const startTime = Date.now();
    let iterations = 0;
    
    while (iterations < this.config.iterationsPerThread && 
           Date.now() - startTime < maxTime) {
      const value = await this.searchIteration(position.clone());
      self.postMessage({
        type: 'partial',
        nodeId,
        value,
        visits: iterations + 1
      });
      
      iterations++;
    }
    
    return value;
  }

  async searchIteration(position) {
    // Simplified single-threaded MCTS for worker
    let node = new MCTSNode(null, null, position);
    const path = [node];
    
    // Selection
    while (node.isFullyExpanded() && !node.isTerminal) {
      node = this.selectChild(node);
      path.push(node);
    }
    
    // Expansion
    if (!node.isTerminal) {
      await this.expandNode(node);
      if (node.children.length > 0) {
        node = node.children[0];
        path.push(node);
      }
    }
    
    // Simulation
    const value = await this.simulate(node.position);
    
    // Backpropagation
    for (const n of path) {
      n.update(value);
    }
    
    return value;
  }

  // ... (same helper methods as main class)
}

////////
// time-manager
class TimeManager {
    constructor(engine) {
        this.engine = engine;
        this.timeBudget = 0;
        this.panicTime = 0;
        this.maxNodes = Infinity;
        this.startTime = 0;
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.bestMoveChanges = 0;
        this.lastBestMove = null;
        this.pvStability = 0;
        
        // Time allocation factors
        this.OPTIMAL_TIME_FACTOR = 0.7;
        this.PANIC_TIME_FACTOR = 0.1;
        this.MAX_TIME_FACTOR = 0.95;
        this.MIN_TIME_MS = 50;
    }

    init({ wtime, btime, winc, binc, movestogo, movetime, depth, nodes, infinite }) {
        this.startTime = Date.now();
        
        if (infinite || depth || nodes) {
            this.timeBudget = Infinity;
            this.panicTime = Infinity;
            this.maxNodes = nodes || Infinity;
            return;
        }

        if (movetime) {
            this.timeBudget = movetime;
            this.panicTime = Math.min(movetime * this.PANIC_TIME_FACTOR, btime ? btime * 0.1 : wtime * 0.1);
            return;
        }

        const timeLeft = this.engine.side === this.engine.COLORS.WHITE ? wtime : btime;
        const increment = this.engine.side === this.engine.COLORS.WHITE ? winc : binc;
        const movesToGo = movestogo || this.estimateMovesToGo();

        // Base time calculation
        let baseTime = timeLeft / movesToGo + increment * 0.8;
        
        // Adjust for game phase (spend more time in complex positions)
        const phase = this.engine.gamePhase() / 256;
        baseTime *= (1.3 - phase * 0.4); // More time in middlegame
        
        // Adjust for material imbalance
        const materialDiff = Math.abs(this.engine.evaluator.evalMaterial(this.engine, 0));
        baseTime *= (1.0 + Math.min(0.5, materialDiff / 800));
        
        // Adjust for position complexity
        baseTime *= (1.0 + this.calculateComplexity() * 0.5);
        
        // Final time budget
        this.timeBudget = Math.max(
            this.MIN_TIME_MS,
            Math.min(timeLeft * this.MAX_TIME_FACTOR, baseTime * this.OPTIMAL_TIME_FACTOR)
        );
        
        // Panic time is 20% of budget or 10% of remaining, whichever is smaller
        this.panicTime = Math.min(timeLeft * 0.1, this.timeBudget * 0.2);
        
        // Node limit based on time control
        this.maxNodes = timeLeft < 30000 ? 1e6 : 5e6;
        
        // Reset tracking variables
        this.lastScore = 0;
        this.scoreDrops = 0;
        this.bestMoveChanges = 0;
        this.pvStability = 0;
    }

    shouldStop(nodes, depth) {
        const elapsed = Date.now() - this.startTime;
        
        // Hard stop conditions
        if (elapsed >= this.timeBudget) return true;
        if (nodes >= this.maxNodes) return true;
        
        // Early stopping conditions when in panic mode
        if (elapsed > this.panicTime && depth > 1) {
            return true;
        }
        
        // Check for score drops
        const currentScore = this.engine.lastScore;
        if (currentScore < this.lastScore - 100) {
            this.scoreDrops++;
            if (this.scoreDrops >= 2 && elapsed > this.timeBudget * 0.3) {
                return true;
            }
        }
        
        // Check PV stability
        const currentBestMove = this.engine.pvTable[0][0];
        if (currentBestMove) {
            if (this.lastBestMove && this.isSameMove(currentBestMove, this.lastBestMove)) {
                this.pvStability++;
            } else {
                this.pvStability = 0;
            }
            this.lastBestMove = currentBestMove;
            
            if (this.pvStability >= 3 && elapsed > this.timeBudget * 0.5) {
                return true;
            }
        }
        
        // Update last score for next iteration
        this.lastScore = currentScore;
        
        return false;
    }

    calculateComplexity() {
        let complexity = 0;
        
        // Material imbalance
        const materialDiff = Math.abs(
            this.engine.evaluator.evalMaterial(this.engine, 0) - 
            this.engine.evaluator.evalMaterial(this.engine, 1)
        );
        complexity += Math.min(0.3, materialDiff / 500);
        
        // Pawn structure
        complexity += Math.min(0.4, Math.abs(this.engine.pawnCache.evaluate(this.engine)) / 200);
        
        // Mobility
        complexity += Math.min(0.3, Math.abs(this.engine.evaluateMobility()) / 150);
        
        // King safety
        complexity += Math.min(0.4, Math.abs(this.engine.evaluateKingSafety()) / 100);
        
        return Math.min(1, complexity);
    }

    estimateMovesToGo() {
        const phase = this.engine.gamePhase() / 256;
        const material = this.engine.evaluator.evalMaterial(this.engine, 0);
        
        // Fewer moves in endgame, more in imbalanced positions
        let movesToGo = 30 - phase * 10;
        
        // Adjust for material imbalance
        if (Math.abs(material) > 300) {
            movesToGo -= 5;
        }
        
        // Adjust for time remaining
        const timeLeft = Math.min(
            this.engine.side === this.engine.COLORS.WHITE ? this.engine.wtime : this.engine.btime,
            60000
        );
        if (timeLeft < 30000) {
            movesToGo = Math.max(10, movesToGo - 5);
        }
        
        return Math.max(10, Math.min(40, movesToGo));
    }

    isSameMove(a, b) {
        return a && b && a.from === b.from && a.to === b.to && 
               (!a.promotion || a.promotion === b.promotion);
    }

    // For UCI time reporting
    getSearchInfo() {
        return {
            time: Date.now() - this.startTime,
            nodes: this.engine.nodes,
            depth: this.engine.seldepth,
            nps: Math.floor(this.engine.nodes / ((Date.now() - this.startTime) / 1000)) || 0,
            score: this.engine.lastScore,
            pv: this.engine.pvTable[0]?.map(m => this.engine.moveToUCI(m)).join(' ') || ''
        };
    }
}
///////////
class YBWCSearcher {
    constructor(engine, threads = 4) {
        this.engine = engine;
        this.threads = threads;
        this.workers = [];
        this.taskQueue = [];
        this.activeTasks = 0;
        this.globalStop = false;
        this.sharedTT = new SharedArrayBuffer(engine.TT_SIZE_MB * 1024 * 1024);
        this.initWorkers();
    }

    initWorkers() {
        if (typeof Worker === 'undefined') {
            console.warn('Web Workers not available, falling back to single-threaded');
            this.threads = 1;
            return;
        }

        const workerCode = `
            ${this.engine.toString()}
            const workerEngine = new SKY5LChess();
            onmessage = async (e) => {
                const { type, taskId, depth, alpha, beta, pvNode, moves } = e.data;
                if (type === 'search') {
                    const result = await workerEngine.ybwcSearch(depth, alpha, beta, pvNode, moves);
                    postMessage({ type: 'result', taskId, ...result });
                } else if (type === 'stop') {
                    workerEngine.stopSearch = true;
                }
            };
        `;

        for (let i = 0; i < this.threads; i++) {
            const blob = new Blob([workerCode], { type: 'application/javascript' });
            const worker = new Worker(URL.createObjectURL(blob));
            worker.onmessage = (e) => this.handleWorkerResponse(e.data);
            this.workers.push(worker);
        }
    }

    async search(position, depth, alpha, beta) {
        this.globalStop = false;
        this.taskQueue = [];
        this.activeTasks = 0;

        // Main thread searches first move
        const moves = position.generateMoves();
        const firstMove = moves[0];
        const undo = position.makeMove(firstMove);
        let bestScore = -this.engine.INFINITY;
        let bestMove = firstMove;

        // Search first move sequentially
        const score = -await this.ybwcSearch(depth - 1, -beta, -alpha, false);
        position.undoMove(firstMove, undo);

        if (score > bestScore) {
            bestScore = score;
            if (score > alpha) {
                alpha = score;
                if (alpha >= beta) return { score: beta, move: firstMove }; // Cutoff
            }
        }

        // Distribute remaining moves to workers (YBWC)
        for (let i = 1; i < moves.length; i++) {
            if (this.globalStop) break;

            const move = moves[i];
            const taskId = performance.now() + i;

            // Wait if too many active tasks (YBWC throttling)
            while (this.activeTasks >= this.threads - 1) {
                await new Promise(resolve => setTimeout(resolve, 1));
            }

            this.activeTasks++;
            this.workers[i % this.workers.length].postMessage({
                type: 'search',
                taskId,
                depth: depth - 1,
                alpha: -beta,
                beta: -alpha,
                pvNode: false,
                moves: [move]
            });

            this.taskQueue.push({ taskId, move, resolve: null });
        }

        // Collect results
        while (this.taskQueue.length > 0 && !this.globalStop) {
            const result = await this.waitForResult();
            if (result.score > bestScore) {
                bestScore = result.score;
                bestMove = result.move;
                if (bestScore > alpha) {
                    alpha = bestScore;
                    if (alpha >= beta) {
                        this.globalStop = true; // Beta cutoff
                        break;
                    }
                }
            }
        }

        return { score: bestScore, move: bestMove };
    }

    waitForResult() {
        return new Promise(resolve => {
            const task = this.taskQueue.find(t => !t.resolve);
            if (task) task.resolve = resolve;
        });
    }

    handleWorkerResponse(data) {
        const task = this.taskQueue.find(t => t.taskId === data.taskId);
        if (task) {
            this.activeTasks--;
            if (task.resolve) task.resolve(data);
            this.taskQueue = this.taskQueue.filter(t => t.taskId !== data.taskId);
        }
    }

    stopSearch() {
        this.globalStop = true;
        this.workers.forEach(w => w.postMessage({ type: 'stop' }));
    }
}

////////////
// probcut
class ProbCut {
    constructor(engine) {
        this.engine = engine;
        
        // ProbCut configuration
        this.MIN_DEPTH = 4;
        this.MARGIN_BASE = 80;
        this.MARGIN_DEPTH_FACTOR = 50;
        this.REDUCTION = 4;
        this.VERIFICATION_REDUCTION = 2;
        
        // Adaptive margin factors
        this.IMPROVING_FACTOR = 0.8;
        this.PV_NODE_FACTOR = 1.2;
        this.ENDGAME_FACTOR = 1.3;
        
        // Statistics
        this.cutoffs = 0;
        this.failHigh = 0;
        this.failLow = 0;
    }

    async probe(depth, beta) {
        // Early exit conditions
        if (depth < this.MIN_DEPTH) return null;
        if (this.engine.isInCheck()) return null;
        if (Math.abs(beta - this.engine.alpha) !== 1) return null;
        
        // Calculate ProbCut margin (depth-sensitive)
        const margin = this.calculateMargin(depth);
        const probCutBeta = beta + margin;
        
        // Generate and order moves
        const moves = this.engine.generateMoves();
        this.engine.moveOrdering.orderMoves(moves, null, depth, this.engine);
        
        // Multi-phase ProbCut implementation
        let probCutScore = null;
        
        // Phase 1: Quick preliminary search
        const preliminaryScore = await this.preliminarySearch(depth, probCutBeta, moves);
        if (preliminaryScore === null) return null;
        
        // Phase 2: Full verification if promising
        if (preliminaryScore >= probCutBeta) {
            probCutScore = await this.verificationSearch(depth, probCutBeta, beta, moves);
            if (probCutScore >= probCutBeta) {
                this.cutoffs++;
                return probCutScore;
            } else {
                this.failLow++;
            }
        } else {
            this.failHigh++;
        }
        
        return null;
    }

    async preliminarySearch(depth, probCutBeta, moves) {
        let bestScore = -this.engine.INFINITY;
        const probCutDepth = depth - this.REDUCTION;
        
        // Search first few moves with reduced depth
        const maxMoves = Math.min(3, moves.length);
        for (let i = 0; i < maxMoves; i++) {
            const move = moves[i];
            
            // SEE pruning for captures
            if (move.captured && !this.engine.see(move, -margin + (beta - probCutBeta))) {
                continue;
            }
            
            const undo = this.engine.makeMove(move);
            const score = -await this.engine.search(
                probCutDepth,
                -probCutBeta,
                -probCutBeta + 1,
                true
            );
            this.engine.undoMove(move, undo);
            
            if (score >= probCutBeta) {
                return score;
            }
            
            bestScore = Math.max(bestScore, score);
        }
        
        return bestScore;
    }

    async verificationSearch(depth, probCutBeta, beta, moves) {
        const verificationDepth = depth - this.VERIFICATION_REDUCTION;
        let bestScore = -this.engine.INFINITY;
        
        // Search promising moves with smaller reduction
        const maxMoves = Math.min(6, moves.length);
        for (let i = 0; i < maxMoves; i++) {
            const move = moves[i];
            
            // SEE pruning with tighter margin
            if (move.captured && !this.engine.see(move, -margin + (beta - probCutBeta) / 2)) {
                continue;
            }
            
            const undo = this.engine.makeMove(move);
            const score = -await this.engine.search(
                verificationDepth,
                -probCutBeta,
                -probCutBeta + 1,
                true
            );
            this.engine.undoMove(move, undo);
            
            if (score >= probCutBeta) {
                return score;
            }
            
            bestScore = Math.max(bestScore, score);
        }
        
        return bestScore;
    }

    calculateMargin(depth) {
        // Base margin
        let margin = this.MARGIN_BASE + this.MARGIN_DEPTH_FACTOR * Math.log2(depth);
        
        // Adjust for game phase
        const phase = this.engine.gamePhase() / 256;
        if (phase > 0.7) { // Endgame
            margin *= this.ENDGAME_FACTOR;
        }
        
        // Adjust for PV nodes
        if (this.engine.pvTable[0]?.length > 0) {
            margin *= this.PV_NODE_FACTOR;
        }
        
        // Adjust for improving positions
        const improving = this.engine.evaluate() > 
            (this.engine.stack.length >= 2 ? this.engine.stack[this.engine.stack.length - 2].staticEval : -this.engine.INFINITY);
        if (improving) {
            margin *= this.IMPROVING_FACTOR;
        }
        
        return Math.floor(margin);
    }

    getStatistics() {
        return {
            cutoffs: this.cutoffs,
            failHigh: this.failHigh,
            failLow: this.failLow,
            efficiency: this.cutoffs / Math.max(1, this.cutoffs + this.failHigh + this.failLow)
        };
    }
}

////////////////////////////////////
// movegen
class MoveGenerator {
    constructor(engine) {
        this.engine = engine;
        this.attackTables = new AttackTables(engine);
        this.pinInfo = new PinDetection(engine);
        
        // Precomputed move patterns
        this.knightMoves = this.precomputeKnightMoves();
        this.kingMoves = this.precomputeKingMoves();
        this.pawnAttacks = this.precomputePawnAttacks();
    }

    generateMoves(includeQuiets = true) {
        const moves = [];
        const us = this.engine.side;
        const them = us ^ 1;
        const kingSquare = this.engine.bitScanForward(
            this.engine.bitboards[us * 6 + this.engine.PIECE_TYPES.KING - 1]
        );
        
        // Detect pins and checks
        const { pinnedPieces, checkers } = this.pinInfo.detect(kingSquare, us);
        const inCheck = checkers !== 0n;
        const doubleCheck = this.engine.popCount(checkers) > 1;
        
        // Generate moves based on game state
        if (inCheck) {
            this.generateEvasions(moves, kingSquare, checkers, pinnedPieces, doubleCheck);
        } else {
            if (includeQuiets) {
                this.generateQuietMoves(moves, kingSquare, pinnedPieces);
            }
            this.generateCaptures(moves, kingSquare, pinnedPieces);
            this.generateSpecialMoves(moves, kingSquare, pinnedPieces);
        }

        return moves;
    }

    generateEvasions(moves, kingSquare, checkers, pinnedPieces, doubleCheck) {
        const us = this.engine.side;
        const them = us ^ 1;
        
        // King moves - must move out of attack
        this.generateKingMoves(moves, kingSquare, true);
        
        // If double check, only king moves are legal
        if (doubleCheck) return;
        
        // Block or capture the checking piece
        const checkerSquare = this.engine.bitScanForward(checkers);
        const checkerPiece = this.engine.getPieceAt(checkerSquare, them);
        const checkerMask = this.getEvasionMask(kingSquare, checkerSquare, checkerPiece);
        
        // Generate blocking moves or captures of checking piece
        this.generateBlockingMoves(moves, checkerMask, pinnedPieces);
    }

    generateQuietMoves(moves, kingSquare, pinnedPieces) {
        const us = this.engine.side;
        
        // Pawn pushes
        this.generatePawnPushes(moves, kingSquare, pinnedPieces);
        
        // Knight moves
        this.generatePieceMoves(
            moves, 
            this.engine.PIECE_TYPES.KNIGHT, 
            this.knightMoves, 
            kingSquare, 
            pinnedPieces,
            false
        );
        
        // Bishop moves
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.BISHOP,
            kingSquare,
            pinnedPieces,
            false
        );
        
        // Rook moves
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.ROOK,
            kingSquare,
            pinnedPieces,
            false
        );
        
        // Queen moves
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.QUEEN,
            kingSquare,
            pinnedPieces,
            false
        );
        
        // King moves (non-captures)
        this.generateKingMoves(moves, kingSquare, false);
        
        // Castling
        this.generateCastling(moves, kingSquare);
    }

    generateCaptures(moves, kingSquare, pinnedPieces) {
        const us = this.engine.side;
        
        // Pawn captures
        this.generatePawnCaptures(moves, kingSquare, pinnedPieces);
        
        // Knight captures
        this.generatePieceMoves(
            moves, 
            this.engine.PIECE_TYPES.KNIGHT, 
            this.knightMoves, 
            kingSquare, 
            pinnedPieces,
            true
        );
        
        // Bishop captures
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.BISHOP,
            kingSquare,
            pinnedPieces,
            true
        );
        
        // Rook captures
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.ROOK,
            kingSquare,
            pinnedPieces,
            true
        );
        
        // Queen captures
        this.generateSliderMoves(
            moves,
            this.engine.PIECE_TYPES.QUEEN,
            kingSquare,
            pinnedPieces,
            true
        );
        
        // King captures
        this.generateKingMoves(moves, kingSquare, true);
    }

    generateSpecialMoves(moves, kingSquare, pinnedPieces) {
        // En passant
        if (this.engine.epSquare >= 0) {
            this.generateEnPassant(moves, kingSquare, pinnedPieces);
        }
        
        // Promotions (already generated as part of pawn pushes/captures)
    }

    // Helper generation methods
    generatePawnPushes(moves, kingSquare, pinnedPieces) {
        const us = this.engine.side;
        const them = us ^ 1;
        const pawns = this.engine.bitboards[us * 6 + this.engine.PIECE_TYPES.PAWN - 1];
        const empty = ~this.engine.occupancy[2];
        const promotionRank = us === this.engine.COLORS.WHITE ? 7 : 0;
        
        let pawnBB = pawns;
        while (pawnBB) {
            const from = this.engine.bitScanForward(pawnBB);
            pawnBB &= pawnBB - 1n;
            
            // Check if pawn is pinned
            const isPinned = pinnedPieces & (1n << BigInt(from));
            if (isPinned) continue;
            
            const push1 = from + (us === this.engine.COLORS.WHITE ? 8 : -8);
            if (empty & (1n << BigInt(push1))) {
                // Single push
                if (Math.floor(push1 / 8) === promotionRank) {
                    this.addPromotions(moves, from, push1, this.engine.PIECE_TYPES.PAWN, 0);
                } else {
                    this.addMove(moves, from, push1, this.engine.PIECE_TYPES.PAWN, 0);
                    
                    // Double push
                    const rank = Math.floor(from / 8);
                    const push2 = from + (us === this.engine.COLORS.WHITE ? 16 : -16);
                    if ((us === this.engine.COLORS.WHITE && rank === 1) || 
                        (us === this.engine.COLORS.BLACK && rank === 6)) {
                        if (empty & (1n << BigInt(push2))) {
                            this.addMove(moves, from, push2, this.engine.PIECE_TYPES.PAWN, 0);
                        }
                    }
                }
            }
        }
    }

    generatePawnCaptures(moves, kingSquare, pinnedPieces) {
        const us = this.engine.side;
        const them = us ^ 1;
        const pawns = this.engine.bitboards[us * 6 + this.engine.PIECE_TYPES.PAWN - 1];
        const enemyPieces = this.engine.occupancy[them];
        const promotionRank = us === this.engine.COLORS.WHITE ? 7 : 0;
        
        let pawnBB = pawns;
        while (pawnBB) {
            const from = this.engine.bitScanForward(pawnBB);
            pawnBB &= pawnBB - 1n;
            
            // Check if pawn is pinned
            const isPinned = pinnedPieces & (1n << BigInt(from));
            
            // Generate captures
            const attacks = this.pawnAttacks[us][from] & enemyPieces;
            let attackBB = attacks;
            while (attackBB) {
                const to = this.engine.bitScanForward(attackBB);
                attackBB &= attackBB - 1n;
                
                // Check if capture is legal for pinned pawn
                if (isPinned && !this.isMoveAlongPinRay(from, to, kingSquare)) {
                    continue;
                }
                
                const captured = this.engine.getPieceAt(to, them);
                if (Math.floor(to / 8) === promotionRank) {
                    this.addPromotions(moves, from, to, this.engine.PIECE_TYPES.PAWN, captured);
                } else {
                    this.addMove(moves, from, to, this.engine.PIECE_TYPES.PAWN, captured);
                }
            }
        }
    }

    generateEnPassant(moves, kingSquare, pinnedPieces) {
        const us = this.engine.side;
        const them = us ^ 1;
        const epSquare = this.engine.epSquare;
        const pawns = this.engine.bitboards[us * 6 + this.engine.PIECE_TYPES.PAWN - 1];
        
        // Get pawns that can capture en passant
        const attackers = pawns & this.pawnAttacks[them][epSquare];
        let attackerBB = attackers;
        
        while (attackerBB) {
            const from = this.engine.bitScanForward(attackerBB);
            attackerBB &= attackerBB - 1n;
            
            // Check if pawn is pinned
            if (pinnedPieces & (1n << BigInt(from))) {
                // Special check for en passant pins
                if (!this.isEnPassantLegal(from, epSquare, kingSquare, us)) {
                    continue;
                }
            }
            
            this.addMove(moves, from, epSquare, this.engine.PIECE_TYPES.PAWN, 
                        this.engine.PIECE_TYPES.PAWN, this.engine.MOVE_FLAGS.ENPASSANT);
        }
    }

    generatePieceMoves(moves, pieceType, moveTable, kingSquare, pinnedPieces, capturesOnly) {
        const us = this.engine.side;
        const them = us ^ 1;
        const pieces = this.engine.bitboards[us * 6 + pieceType - 1];
        const targets = capturesOnly ? this.engine.occupancy[them] : ~this.engine.occupancy[us];
        
        let pieceBB = pieces;
        while (pieceBB) {
            const from = this.engine.bitScanForward(pieceBB);
            pieceBB &= pieceBB - 1n;
            
            // Check if piece is pinned
            const isPinned = pinnedPieces & (1n << BigInt(from));
            
            // Get possible moves
            let movesBB = moveTable[from] & targets;
            
            // For pinned pieces, only allow moves along the pin ray
            if (isPinned) {
                movesBB &= this.pinInfo.getPinRay(from, kingSquare);
            }
            
            // Generate moves
            while (movesBB) {
                const to = this.engine.bitScanForward(movesBB);
                movesBB &= movesBB - 1n;
                
                const captured = capturesOnly ? this.engine.getPieceAt(to, them) : 0;
                this.addMove(moves, from, to, pieceType, captured);
            }
        }
    }

    generateSliderMoves(moves, pieceType, kingSquare, pinnedPieces, capturesOnly) {
        const us = this.engine.side;
        const them = us ^ 1;
        const pieces = this.engine.bitboards[us * 6 + pieceType - 1];
        const targets = capturesOnly ? this.engine.occupancy[them] : ~this.engine.occupancy[us];
        
        let pieceBB = pieces;
        while (pieceBB) {
            const from = this.engine.bitScanForward(pieceBB);
            pieceBB &= pieceBB - 1n;
            
            // Check if piece is pinned
            const isPinned = pinnedPieces & (1n << BigInt(from));
            
            // Get attack mask
            let attacks = this.attackTables.getSliderAttacks(pieceType, from);
            attacks &= targets;
            
            // For pinned pieces, only allow moves along the pin ray
            if (isPinned) {
                attacks &= this.pinInfo.getPinRay(from, kingSquare);
            }
            
            // Generate moves
            while (attacks) {
                const to = this.engine.bitScanForward(attacks);
                attacks &= attacks - 1n;
                
                const captured = capturesOnly ? this.engine.getPieceAt(to, them) : 0;
                this.addMove(moves, from, to, pieceType, captured);
            }
        }
    }

    generateKingMoves(moves, fromSquare, capturesOnly) {
        const us = this.engine.side;
        const them = us ^ 1;
        const targets = capturesOnly ? this.engine.occupancy[them] : ~this.engine.occupancy[us];
        
        // Normal king moves
        let movesBB = this.kingMoves[fromSquare] & targets;
        while (movesBB) {
            const to = this.engine.bitScanForward(movesBB);
            movesBB &= movesBB - 1n;
            
            // Make sure destination is not attacked
            if (this.attackTables.isSquareAttacked(to, them)) continue;
            
            const captured = capturesOnly ? this.engine.getPieceAt(to, them) : 0;
            this.addMove(moves, fromSquare, to, this.engine.PIECE_TYPES.KING, captured);
        }
    }

    generateCastling(moves, kingSquare) {
        const us = this.engine.side;
        const them = us ^ 1;
        
        if (this.engine.isInCheck()) return;
        
        const castlingRights = this.engine.castling;
        if (!castlingRights) return;
        
        // Generate kingside castling
        if (castlingRights & (us === this.engine.COLORS.WHITE ? 0b0001 : 0b0100)) {
            this.generateCastle(moves, kingSquare, true, us, them);
        }
        
        // Generate queenside castling
        if (castlingRights & (us === this.engine.COLORS.WHITE ? 0b0010 : 0b1000)) {
            this.generateCastle(moves, kingSquare, false, us, them);
        }
    }

    generateCastle(moves, kingSquare, kingside, us, them) {
        const [rookFrom, rookTo, kingTo, emptySquares, safeSquares] = 
            this.getCastleSquares(kingSquare, kingside, us);
        
        // Check if squares are empty and not attacked
        if ((this.engine.occupancy[2] & emptySquares) !== 0n) return;
        if (this.attackTables.areSquaresAttacked(safeSquares, them)) return;
        
        this.addMove(
            moves, 
            kingSquare, 
            kingTo, 
            this.engine.PIECE_TYPES.KING, 
            0, 
            this.engine.MOVE_FLAGS.CASTLING,
            rookFrom,
            rookTo
        );
    }

    // Helper methods
    addMove(moves, from, to, piece, captured, flags = 0, extra1 = 0, extra2 = 0) {
        moves.push({
            from,
            to,
            piece,
            captured,
            promotion: 0,
            flags,
            extra1,
            extra2,
            score: 0
        });
    }

    addPromotions(moves, from, to, piece, captured) {
        for (const promo of [
            this.engine.PIECE_TYPES.QUEEN,
            this.engine.PIECE_TYPES.ROOK,
            this.engine.PIECE_TYPES.BISHOP,
            this.engine.PIECE_TYPES.KNIGHT
        ]) {
            this.addMove(
                moves, 
                from, 
                to, 
                piece, 
                captured, 
                this.engine.MOVE_FLAGS.PROMOTION,
                promo
            );
        }
    }

    // Precomputation methods
    precomputeKnightMoves() {
        const moves = new Array(64).fill(0n);
        const deltas = [15, 17, 10, -6, -15, -17, -10, 6];
        
        for (let square = 0; square < 64; square++) {
            let attacks = 0n;
            for (const delta of deltas) {
                const to = square + delta;
                if (to >= 0 && to < 64 && Math.abs((to % 8) - (square % 8)) <= 2) {
                    attacks |= 1n << BigInt(to);
                }
            }
            moves[square] = attacks;
        }
        
        return moves;
    }

    precomputeKingMoves() {
        const moves = new Array(64).fill(0n);
        const deltas = [9, 8, 7, 1, -1, -7, -8, -9];
        
        for (let square = 0; square < 64; square++) {
            let attacks = 0n;
            for (const delta of deltas) {
                const to = square + delta;
                if (to >= 0 && to < 64 && Math.abs((to % 8) - (square % 8)) <= 1) {
                    attacks |= 1n << BigInt(to);
                }
            }
            moves[square] = attacks;
        }
        
        return moves;
    }

    precomputePawnAttacks() {
        const attacks = Array.from({length: 2}, () => new Array(64).fill(0n));
        
        for (let square = 0; square < 64; square++) {
            // White pawn attacks
            if (square > 7) {
                if (square % 8 > 0) attacks[0][square] |= 1n << BigInt(square - 9);
                if (square % 8 < 7) attacks[0][square] |= 1n << BigInt(square - 7);
            }
            
            // Black pawn attacks
            if (square < 56) {
                if (square % 8 > 0) attacks[1][square] |= 1n << BigInt(square + 7);
                if (square % 8 < 7) attacks[1][square] |= 1n << BigInt(square + 9);
            }
        }
        
        return attacks;
    }
}

// Helper classes
class AttackTables {
    constructor(engine) {
        this.engine = engine;
        this.initialize();
    }
    
    initialize() {
        // Initialize attack tables for sliders
    }
    
    getSliderAttacks(pieceType, square) {
        // Return attack bitboard for slider piece
    }
    
    isSquareAttacked(square, byColor) {
        // Check if square is attacked by given color
    }
    
    areSquaresAttacked(squares, byColor) {
        // Check if any of squares are attacked
    }
}

class PinDetection {
    constructor(engine) {
        this.engine = engine;
    }
    
    detect(kingSquare, color) {
        // Detect pinned pieces and checkers
    }
    
    getPinRay(from, kingSquare) {
        // Get bitboard of squares along pin ray
    }
}

//////////////////////

// evaluation
 class Evaluation {
    constructor(engine) {
        this.engine = engine;
        
        // Initialize sub-components
        this.materialEvaluator = new MaterialEvaluator(engine);
        this.pawnStructureEvaluator = new PawnStructureEvaluator(engine);
        this.mobilityEvaluator = new MobilityEvaluator(engine);
        this.kingSafetyEvaluator = new KingSafetyEvaluator(engine);
        this.pieceSquareTables = new PieceSquareTables(engine);
        this.threatEvaluator = new ThreatEvaluator(engine);
        this.passedPawnEvaluator = new PassedPawnEvaluator(engine);
        this.spaceEvaluator = new SpaceEvaluator(engine);
        
        // Initialize NNUE
        this.nnue = new NNUE_HalfKAv2_Extended();
        this.nnueReady = false;
        
        // Evaluation cache
        this.evalCache = new Map();
        this.cacheHits = 0;
        this.cacheMisses = 0;
    }

    async init() {
        try {
            await this.nnue.loadModel('nnue_halfkav2_ext.bin');
            this.nnueReady = true;
        } catch (e) {
            console.error("NNUE failed to load, falling back to classical evaluation");
            this.nnueReady = false;
        }
    }

    evaluate() {
        // Check for immediate termination conditions
        if (this.engine.isDrawn()) return this.getDrawScore();
        
        // Try cache first
        const cacheKey = this.engine.hash;
        if (this.evalCache.has(cacheKey)) {
            this.cacheHits++;
            return this.evalCache.get(cacheKey);
        }
        this.cacheMisses++;
        
        // Get game phase (0 = opening, 256 = endgame)
        const phase = this.engine.gamePhase();
        const phaseFactor = phase / 256;
        
        // Choose evaluation method based on phase and NNUE availability
        let score;
        if (this.nnueReady && phaseFactor > 0.7) {
            // Pure NNUE in endgame
            score = this.nnue.evaluate(this.engine);
        } else if (this.nnueReady && phaseFactor > 0.3) {
            // Hybrid evaluation in late middlegame
            const nnueScore = this.nnue.evaluate(this.engine);
            const classicalScore = this.classicalEvaluation(phaseFactor);
            score = (nnueScore * 0.7 + classicalScore * 0.3);
        } else {
            // Classical evaluation in opening/early middlegame
            score = this.classicalEvaluation(phaseFactor);
        }
        
        // Scale score for color
        score = this.engine.side === this.engine.COLORS.WHITE ? score : -score;
        
        // Store in cache
        this.evalCache.set(cacheKey, score);
        if (this.evalCache.size > 10000) this.evalCache.clear();
        
        return score;
    }

    classicalEvaluation(phaseFactor) {
        let score = 0;
        
        // 1. Material evaluation
        score += this.materialEvaluator.evaluate(phaseFactor);
        
        // 2. Piece-square tables
        score += this.pieceSquareTables.evaluate(phaseFactor);
        
        // 3. Pawn structure evaluation
        score += this.pawnStructureEvaluator.evaluate();
        
        // 4. Mobility evaluation
        score += this.mobilityEvaluator.evaluate(phaseFactor);
        
        // 5. King safety evaluation
        score += this.kingSafetyEvaluator.evaluate(phaseFactor);
        
        // 6. Passed pawn evaluation
        score += this.passedPawnEvaluator.evaluate(phaseFactor);
        
        // 7. Space evaluation
        score += this.spaceEvaluator.evaluate(phaseFactor);
        
        // 8. Threat evaluation
        score += this.threatEvaluator.evaluate();
        
        // 9. Tempo bonus
        score += 12;
        
        // 10. Contempt factor
        score += this.engine.getDynamicContempt();
        
        return score;
    }

    getDrawScore() {
        const contempt = this.engine.getDynamicContempt();
        return this.engine.side === this.engine.COLORS.WHITE ? contempt : -contempt;
    }

    clearCache() {
        this.evalCache.clear();
        this.cacheHits = 0;
        this.cacheMisses = 0;
    }

    getStatistics() {
        return {
            cacheHits: this.cacheHits,
            cacheMisses: this.cacheMisses,
            cacheHitRate: this.cacheHits / (this.cacheHits + this.cacheMisses + 1),
            nnueReady: this.nnueReady
        };
    }
}

// Sub-components of evaluation
class MaterialEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate(phaseFactor) {
        let score = 0;
        
        for (let piece = this.engine.PIECE_TYPES.PAWN; piece <= this.engine.PIECE_TYPES.QUEEN; piece++) {
            // White material
            const whiteCount = this.engine.popCount(
                this.engine.bitboards[this.engine.COLORS.WHITE * 6 + piece - 1]
            );
            score += whiteCount * this.interpolateValue(piece, phaseFactor);
            
            // Black material
            const blackCount = this.engine.popCount(
                this.engine.bitboards[this.engine.COLORS.BLACK * 6 + piece - 1]
            );
            score -= blackCount * this.interpolateValue(piece, phaseFactor);
        }
        
        // Bishop pair bonus
        if (this.engine.popCount(this.engine.bitboards[this.engine.COLORS.WHITE * 6 + this.engine.PIECE_TYPES.BISHOP - 1]) >= 2) {
            score += 30 * (1 - phaseFactor * 0.5);
        }
        if (this.engine.popCount(this.engine.bitboards[this.engine.COLORS.BLACK * 6 + this.engine.PIECE_TYPES.BISHOP - 1]) >= 2) {
            score -= 30 * (1 - phaseFactor * 0.5);
        }
        
        return score;
    }

    interpolateValue(piece, phaseFactor) {
        return this.engine.PIECE_VALUES[piece][0] * (1 - phaseFactor) + 
               this.engine.PIECE_VALUES[piece][1] * phaseFactor;
    }
}

class PawnStructureEvaluator {
    constructor(engine) {
        this.engine = engine;
        this.pawnHashTable = new Map();
    }

    evaluate() {
        const pawnHash = this.calculatePawnHash();
        if (this.pawnHashTable.has(pawnHash)) {
            return this.pawnHashTable.get(pawnHash);
        }
        
        let score = 0;
        
        // Doubled pawns
        score += this.evaluateDoubledPawns();
        
        // Isolated pawns
        score += this.evaluateIsolatedPawns();
        
        // Pawn chains
        score += this.evaluatePawnChains();
        
        // Store in hash table
        this.pawnHashTable.set(pawnHash, score);
        if (this.pawnHashTable.size > 10000) this.pawnHashTable.clear();
        
        return score;
    }

    evaluateDoubledPawns() {
        // Implementation for doubled pawn evaluation
        // In PawnStructureEvaluator class
    let score = 0;
    
    // Evaluate white doubled pawns
    score -= this.evaluateColorDoubledPawns(this.engine.COLORS.WHITE);
    
    // Evaluate black doubled pawns
    score += this.evaluateColorDoubledPawns(this.engine.COLORS.BLACK);
    
    return score;
}

evaluateColorDoubledPawns(color) {
    const pawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    let doubledPenalty = 0;
    
    // Check each file for doubled pawns
    for (let file = 0; file < 8; file++) {
        const fileMask = this.engine.fileMasks[file];
        const pawnsOnFile = this.engine.popCount(pawns & fileMask);
        
        if (pawnsOnFile > 1) {
            // The penalty increases with each additional pawn on the file
            doubledPenalty += this.getDoubledPawnPenalty(pawnsOnFile, file, color);
        }
    }
    
    return doubledPenalty;
}

getDoubledPawnPenalty(pawnCount, file, color) {
    // Base penalty for any doubled pawns
    let penalty = 10;
    
    // Additional penalty for tripled or more pawns
    if (pawnCount >= 3) {
        penalty += 20 * (pawnCount - 2);
    }
    
    // Adjust penalty based on file and game phase
    const phase = this.engine.gamePhase() / 256;
    
    // More severe penalty in endgame
    penalty *= (0.7 + phase * 0.6);
    
    // Less penalty on semi-open files (no enemy pawns)
    if (!this.hasEnemyPawnsOnFile(color ^ 1, file)) {
        penalty *= 0.7;
    }
    
    // Less penalty on central files where they might be useful
    if (file >= 2 && file <= 5) {
        penalty *= 0.8;
    }
    
    // Less penalty if the pawns are connected
    if (this.areDoubledPawnsConnected(color, file)) {
        penalty *= 0.6;
    }
    
    return Math.round(penalty);
}

hasEnemyPawnsOnFile(enemyColor, file) {
    const enemyPawns = this.engine.bitboards[enemyColor * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    return (enemyPawns & this.engine.fileMasks[file]) !== 0n;
}

areDoubledPawnsConnected(color, file) {
    const pawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    const filePawns = pawns & this.engine.fileMasks[file];
    
    let pawnBB = filePawns;
    while (pawnBB) {
        const sq = this.engine.bitScanForward(pawnBB);
        pawnBB &= pawnBB - 1n;
        
        // Check if any pawn on this file is protected by another pawn
        const protectors = this.engine.pawnAttacks[color ^ 1][sq] & filePawns;
        if (protectors !== 0n) {
            return true;
        }
    }
    
    return false;
}

    evaluateIsolatedPawns() {
        // Implementation for isolated pawn evaluation
    }

    evaluatePawnChains() {
        // Implementation for pawn chain evaluation
    }

    calculatePawnHash() {
        // Calculate unique hash for pawn structure
    }
}

class MobilityEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate(phaseFactor) {
        let score = 0;
        
        // Evaluate mobility for each piece type
        score += this.evaluatePieceMobility(this.engine.PIECE_TYPES.KNIGHT, 1, phaseFactor);
        score += this.evaluatePieceMobility(this.engine.PIECE_TYPES.BISHOP, 1, phaseFactor);
        score += this.evaluatePieceMobility(this.engine.PIECE_TYPES.ROOK, 0.5, phaseFactor);
        score += this.evaluatePieceMobility(this.engine.PIECE_TYPES.QUEEN, 0.3, phaseFactor);
        
        return score * (1 - phaseFactor * 0.5); // Mobility more important in opening
    }

    evaluatePieceMobility(pieceType, weight, phaseFactor) {
        // Implementation for piece mobility evaluation
    }
}

class KingSafetyEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate(phaseFactor) {
        if (phaseFactor > 0.7) return 0; // Less important in endgame
        
        let score = 0;
        
        // Evaluate white king safety
        score += this.evaluateKingSafety(this.engine.COLORS.WHITE);
        
        // Evaluate black king safety
        score -= this.evaluateKingSafety(this.engine.COLORS.BLACK);
        
        return score * (1 - phaseFactor * 0.7); // King safety more important in opening
    }

    evaluateKingSafety(color) {
        // Implementation for king safety evaluation
    }
}

class PieceSquareTables {
    constructor(engine) {
        this.engine = engine;
        this.initTables();
    }

    initTables() {
        // Initialize piece-square tables
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
    }

    evaluate(phaseFactor) {
        let score = 0;
        
        // Evaluate for each piece type and color
        for (let color = 0; color < 2; color++) {
            for (let piece = 0; piece < 6; piece++) {
                const sign = color === this.engine.COLORS.WHITE ? 1 : -1;
                let bb = this.engine.bitboards[color * 6 + piece];
                
                while (bb) {
                    const sq = this.engine.bitScanForward(bb);
                    bb &= bb - 1n;
                    
                    // Interpolate between middle-game and end-game PST values
                    const mg = this.middleGameTables[color * 6 + piece][sq];
                    const eg = this.endGameTables[color * 6 + piece][sq];
                    score += sign * (mg * (1 - phaseFactor) + eg * phaseFactor);
                }
            }
        }
        
        return score;
    }
}

class ThreatEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate() {
        let score = 0;
        
        // Evaluate threats for white
        score += this.evaluateThreats(this.engine.COLORS.WHITE, this.engine.COLORS.BLACK);
        
        // Evaluate threats for black
        score -= this.evaluateThreats(this.engine.COLORS.BLACK, this.engine.COLORS.WHITE);
        
        return score;
    }

    evaluateThreats(attacker, defender) {
        // Implementation for threat evaluation
    }
}

class PassedPawnEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate(phaseFactor) {
        let score = 0;
        
        // Evaluate white passed pawns
        score += this.evaluatePassedPawns(this.engine.COLORS.WHITE, phaseFactor);
        
        // Evaluate black passed pawns
        score -= this.evaluatePassedPawns(this.engine.COLORS.BLACK, phaseFactor);
        
        return score * (0.5 + phaseFactor * 0.5); // Passed pawns more important in endgame
    }

    evaluatePassedPawns(color, phaseFactor) {
        // Implementation for passed pawn evaluation
    }
}

class SpaceEvaluator {
    constructor(engine) {
        this.engine = engine;
    }

    evaluate(phaseFactor) {
        if (phaseFactor > 0.5) return 0; // Space not important in endgame
        
        let score = 0;
        
        // Evaluate white space
        score += this.evaluateSpace(this.engine.COLORS.WHITE);
        
        // Evaluate black space
        score -= this.evaluateSpace(this.engine.COLORS.BLACK);
        
        return score * (1 - phaseFactor * 0.5); // Space more important in opening
    }

    evaluateSpace(color) {
        // Implementation for space evaluation
    }
}



///////////////////

// ===================== PREDICTIVE CUTTING =====================
 class PredictiveCutting {
  constructor() {
    // History table for move ordering [from][to][piece]
    this.historyTable = Array.from({length: 64}, () => 
      Array.from({length: 64}, () => 
        new Int16Array(6).fill(0)
      )
    );
    
    // Counter-move history [prevPiece][prevTo][piece][to]
    this.counterMoveHistory = Array.from({length: 6}, () => 
      Array.from({length: 64}, () => 
        Array.from({length: 6}, () => 
          new Int16Array(64).fill(0)
        )
      )
    );
    
    // Butterfly history [from][to]
    this.butterflyHistory = Array.from({length: 64}, () => 
      new Int16Array(64).fill(0)
    );
    
    // Depth-based margins for probcut
    this.probCutMargins = [50, 75, 100, 125, 150, 175, 200];
    
    // Minimum depth for probcut
    this.minProbCutDepth = 4;
    
    // Reduction factors based on depth
    this.reductionFactors = [0, 0, 1, 2, 3, 4, 5, 6];
    
    // Maximum depth for verification search
    this.maxVerificationDepth = 12;
  }

  // Should we attempt a probcut at this node?
  shouldAttemptProbCut(depth, beta, alpha) {
    return depth >= this.minProbCutDepth && 
           beta > alpha + 50 && 
           beta < this.MATE_THRESHOLD;
  }

  // Main probcut function
  async probCut(position, depth, beta, isPVNode) {
    if (!this.shouldAttemptProbCut(depth, beta, position.alpha)) {
      return {shouldCut: false, score: 0};
    }

    const probCutDepth = depth - 4;
    const margin = this.getProbCutMargin(depth);
    const probCutBeta = beta + margin;
    
    // Generate moves with high probability of cutting
    const moves = position.generateMoves();
    this.orderMovesForProbCut(moves, position);
    
    let cutMoves = 0;
    let bestScore = -position.INFINITY;
    
    for (const move of moves) {
      // Skip moves unlikely to cause a cutoff
      if (!this.isLikelyCutMove(move, position, probCutBeta)) {
        continue;
      }
      
      const undo = position.makeMove(move);
      let score;
      
      // Null-move verification for faster pruning
      if (depth >= 6 && !position.isInCheck() && !move.captured && !move.promotion) {
        position.makeNullMove();
        const nullScore = -await position.search(
          probCutDepth - 3, 
          -probCutBeta, 
          -probCutBeta + 1, 
          false
        );
        position.undoNullMove();
        
        if (nullScore >= probCutBeta) {
          position.undoMove(move, undo);
          continue;
        }
      }
      
      // Full probcut search
      score = -await position.search(
        probCutDepth, 
        -probCutBeta, 
        -probCutBeta + 1, 
        false
      );
      
      position.undoMove(move, undo);
      
      if (score >= probCutBeta) {
        // Verification search to reduce errors
        if (depth <= this.maxVerificationDepth) {
          const verifyScore = -await position.search(
            probCutDepth - 1, 
            -probCutBeta - 50, 
            -probCutBeta + 50, 
            false
          );
          
          if (verifyScore >= probCutBeta) {
            return {shouldCut: true, score: probCutBeta};
          }
        } else {
          return {shouldCut: true, score: probCutBeta};
        }
      }
      
      bestScore = Math.max(bestScore, score);
      cutMoves++;
      
      // Early exit if we've checked enough moves
      if (cutMoves >= 3 && bestScore < probCutBeta - margin / 2) {
        break;
      }
    }
    
    return {shouldCut: false, score: bestScore};
  }

  // Order moves by their likelihood to cause a cutoff
  orderMovesForProbCut(moves, position) {
    const ttMove = position.probeTT()?.move;
    
    moves.sort((a, b) => {
      // TT move first
      if (ttMove && a.from === ttMove.from && a.to === ttMove.to) return -1;
      if (ttMove && b.from === ttMove.from && b.to === ttMove.to) return 1;
      
      // Captures ordered by SEE
      if (a.captured && b.captured) {
        return position.see(b) - position.see(a);
      }
      if (a.captured) return -1;
      if (b.captured) return 1;
      
      // Killer moves
      if (position.isKillerMove(a)) return -1;
      if (position.isKillerMove(b)) return 1;
      
      // History heuristic
      const aHistory = this.getHistoryScore(a, position);
      const bHistory = this.getHistoryScore(b, position);
      
      return bHistory - aHistory;
    });
  }

  // Is this move likely to cause a cutoff?
  isLikelyCutMove(move, position, probCutBeta) {
    // Captures with positive SEE
    if (move.captured) {
      return position.see(move) >= 0;
    }
    
    // Promotions are always likely
    if (move.promotion) {
      return true;
    }
    
    // Check moves
    if (position.givesCheck(move)) {
      return true;
    }
    
    // Moves with good history
    const historyScore = this.getHistoryScore(move, position);
    return historyScore > 1000;
  }

  // Get history score for a move
  getHistoryScore(move, position) {
    const piece = move.piece - 1; // Convert to 0-based index
    const from = move.from;
    const to = move.to;
    
    let score = this.historyTable[from][to][piece];
    
    // Counter-move bonus
    if (position.stack.length > 0) {
      const prevMove = position.stack[position.stack.length - 1].move;
      if (prevMove) {
        const prevPiece = prevMove.piece - 1;
        const prevTo = prevMove.to;
        score += this.counterMoveHistory[prevPiece][prevTo][piece][to] / 2;
      }
    }
    
    // Butterfly history
    score += this.butterflyHistory[from][to] / 4;
    
    return score;
  }

  // Update history tables after a cutoff
  updateCutStats(move, depth, success, position) {
    const piece = move.piece - 1;
    const from = move.from;
    const to = move.to;
    const bonus = depth * depth * (success ? 1 : -1);
    
    // Update main history
    this.historyTable[from][to][piece] = Math.max(
      -32768, 
      Math.min(32767, this.historyTable[from][to][piece] + bonus)
    );
    
    // Update counter-move history
    if (position.stack.length > 0) {
      const prevMove = position.stack[position.stack.length - 1].move;
      if (prevMove) {
        const prevPiece = prevMove.piece - 1;
        const prevTo = prevMove.to;
        this.counterMoveHistory[prevPiece][prevTo][piece][to] = Math.max(
          -32768,
          Math.min(32767, this.counterMoveHistory[prevPiece][prevTo][piece][to] + bonus)
        );
      }
    }
    
    // Update butterfly history
    this.butterflyHistory[from][to] = Math.max(
      -32768,
      Math.min(32767, this.butterflyHistory[from][to] + bonus / 2)
    );
  }

  // Get dynamic margin based on depth and position characteristics
  getProbCutMargin(depth) {
    const depthIndex = Math.min(depth - this.minProbCutDepth, this.probCutMargins.length - 1);
    return this.probCutMargins[depthIndex];
  }

  // Get reduction depth for verification search
  getVerificationReduction(depth) {
    return this.reductionFactors[Math.min(depth, this.reductionFactors.length - 1)];
  }

  // Clear history tables (for new search)
  clearHistory() {
    for (let from = 0; from < 64; from++) {
      for (let to = 0; to < 64; to++) {
        this.butterflyHistory[from][to] = 0;
        for (let piece = 0; piece < 6; piece++) {
          this.historyTable[from][to][piece] = 0;
        }
      }
    }
    
    for (let prevPiece = 0; prevPiece < 6; prevPiece++) {
      for (let prevTo = 0; prevTo < 64; prevTo++) {
        for (let piece = 0; piece < 6; piece++) {
          for (let to = 0; to < 64; to++) {
            this.counterMoveHistory[prevPiece][prevTo][piece][to] = 0;
          }
        }
      }
    }
  }
}



////////////////////
// ===================== PAWN STRUCTURE CACHE =====================

class PawnStructureCache {
  constructor() {
    this.cache = new Map();
    this.hashMask = (1n << 64n) - 1n;
    this.resetStats();
  }

  resetStats() {
    this.hits = 0;
    this.misses = 0;
    this.size = 0;
  }

  getStats() {
    return {
      hits: this.hits,
      misses: this.misses,
      size: this.size,
      hitRate: this.hits / (this.hits + this.misses) || 0
    };
  }

  clear() {
    this.cache.clear();
    this.resetStats();
  }

  evaluate(position) {
    const key = position.hash & this.hashMask;
    const entry = this.cache.get(key);
    
    if (entry && entry.hash === position.hash) {
      this.hits++;
      return entry.score;
    }
    
    this.misses++;
    const score = this.evaluatePawnStructure(position);
    
    this.cache.set(key, {
      hash: position.hash,
      score: score
    });
    
    this.size = this.cache.size;
    return score;
  }

  evaluatePawnStructure(position) {
    let score = 0;
    const us = position.side;
    const them = us ^ 1;
    
    // Evaluate white pawns
    score += this.evalPawnsForColor(position, position.WHITE);
    
    // Evaluate black pawns
    score -= this.evalPawnsForColor(position, position.BLACK);
    
    // Adjust for side to move
    return us === position.WHITE ? score : -score;
  }

  evalPawnsForColor(position, color) {
    let score = 0;
    const pawns = position.bitboards[color * 6 + position.PIECE_TYPES.PAWN - 1];
    const enemyPawns = position.bitboards[(color ^ 1) * 6 + position.PIECE_TYPES.PAWN - 1];
    const kingSquare = position.bitScanForward(position.bitboards[color * 6 + position.PIECE_TYPES.KING - 1]);
    
    // Doubled pawns
    for (let file = 0; file < 8; file++) {
      const filePawns = pawns & position.fileMasks[file];
      const count = position.popCount(filePawns);
      if (count > 1) {
        score -= 20 * (count - 1);
      }
    }
    
    // Isolated pawns
    let isolated = pawns;
    while (isolated) {
      const sq = position.bitScanForward(isolated);
      isolated &= isolated - 1n;
      
      const file = sq % 8;
      if (!(pawns & position.isolatedMask[file])) {
        score -= 15;
        
        // Additional penalty if on open file
        if (!(enemyPawns & position.fileMasks[file])) {
          score -= 10;
        }
      }
    }
    
    // Passed pawns
    let passed = pawns;
    while (passed) {
      const sq = position.bitScanForward(passed);
      passed &= passed - 1n;
      
      if (!(enemyPawns & position.passedPawnMasks[color][sq])) {
        const rank = Math.floor(sq / 8);
        const promotionDist = color === position.WHITE ? 7 - rank : rank;
        let pawnValue = 30 + (6 - promotionDist) * 15;
        
        // Bonus for protected passed pawns
        if (color === position.WHITE) {
          if ((position.pawnAttacks[position.BLACK][sq] & pawns)) {
            pawnValue += 20;
          }
        } else {
          if ((position.pawnAttacks[position.WHITE][sq] & pawns)) {
            pawnValue += 20;
          }
        }
        
        // Bonus for king proximity in endgame
        const phase = position.gamePhase() / 256;
        if (phase > 0.7 && kingSquare !== -1) {
          const kingFile = kingSquare % 8;
          const kingRank = Math.floor(kingSquare / 8);
          const pawnFile = sq % 8;
          const pawnRank = Math.floor(sq / 8);
          
          const fileDist = Math.abs(kingFile - pawnFile);
          const rankDist = Math.abs(kingRank - pawnRank);
          const dist = Math.max(fileDist, rankDist);
          
          pawnValue += (7 - dist) * 5;
        }
        
        score += pawnValue;
      }
    }
    
    // Pawn chains and phalanxes
    let chains = pawns;
    while (chains) {
      const sq = position.bitScanForward(chains);
      chains &= chains - 1n;
      
      const file = sq % 8;
      const rank = Math.floor(sq / 8);
      
      // Check for supporting pawns
      if (file > 0) {
        const supportingSq = color === position.WHITE ? sq + 7 : sq - 9;
        if (pawns & (1n << BigInt(supportingSq))) {
          score += 10;
          
          // Bonus for connected passed pawns
          if (!(enemyPawns & position.passedPawnMasks[color][sq]) && 
              !(enemyPawns & position.passedPawnMasks[color][supportingSq])) {
            score += 15;
          }
        }
      }
      
      if (file < 7) {
        const supportingSq = color === position.WHITE ? sq + 9 : sq - 7;
        if (pawns & (1n << BigInt(supportingSq))) {
          score += 10;
          
          // Bonus for connected passed pawns
          if (!(enemyPawns & position.passedPawnMasks[color][sq]) && 
              !(enemyPawns & position.passedPawnMasks[color][supportingSq])) {
            score += 15;
          }
        }
      }
    }
    
    // Pawn storms (for opposite-side castling)
    if (kingSquare !== -1) {
      const kingFile = kingSquare % 8;
      if (kingFile < 3 || kingFile > 5) { // King castled
        const stormFiles = kingFile < 3 ? [2, 3, 4] : [4, 5, 6];
        let stormScore = 0;
        
        for (const file of stormFiles) {
          const filePawns = pawns & position.fileMasks[file];
          if (filePawns) {
            const sq = position.bitScanForward(filePawns);
            const rank = Math.floor(sq / 8);
            const dist = color === position.WHITE ? 7 - rank : rank;
            stormScore += (5 - dist) * 5;
          }
        }
        
        score += stormScore;
      }
    }
    
    return score;
  }

  // Advanced pawn structure evaluation for NNUE
  getPawnStructureFeatures(position) {
    const features = {
      doubledPawns: [0, 0],       // [white, black]
      isolatedPawns: [0, 0],
      passedPawns: [0, 0],
      pawnChains: [0, 0],
      openFiles: [0, 0],
      halfOpenFiles: [0, 0]
    };

    for (let color = 0; color < 2; color++) {
      const pawns = position.bitboards[color * 6 + position.PIECE_TYPES.PAWN - 1];
      const enemyPawns = position.bitboards[(color ^ 1) * 6 + position.PIECE_TYPES.PAWN - 1];

      // Doubled pawns
      for (let file = 0; file < 8; file++) {
        const count = position.popCount(pawns & position.fileMasks[file]);
        if (count > 1) features.doubledPawns[color] += count - 1;
      }

      // Isolated pawns
      let isolated = pawns;
      while (isolated) {
        const sq = position.bitScanForward(isolated);
        isolated &= isolated - 1n;
        const file = sq % 8;
        if (!(pawns & position.isolatedMask[file])) {
          features.isolatedPawns[color]++;
        }
      }

      // Passed pawns
      let passed = pawns;
      while (passed) {
        const sq = position.bitScanForward(passed);
        passed &= passed - 1n;
        if (!(enemyPawns & position.passedPawnMasks[color][sq])) {
          features.passedPawns[color]++;
        }
      }

      // Pawn chains
      let chains = pawns;
      while (chains) {
        const sq = position.bitScanForward(chains);
        chains &= chains - 1n;
        const file = sq % 8;
        
        if (file > 0 && (pawns & position.pawnAttacks[color ^ 1][sq])) {
          features.pawnChains[color]++;
        }
        if (file < 7 && (pawns & position.pawnAttacks[color ^ 1][sq])) {
          features.pawnChains[color]++;
        }
      }
    }

    // Open and half-open files
    for (let file = 0; file < 8; file++) {
      const whitePawns = position.popCount(
        position.bitboards[position.WHITE * 6 + position.PIECE_TYPES.PAWN - 1] & 
        position.fileMasks[file]
      );
      const blackPawns = position.popCount(
        position.bitboards[position.BLACK * 6 + position.PIECE_TYPES.PAWN - 1] & 
        position.fileMasks[file]
      );

      if (whitePawns === 0 && blackPawns === 0) {
        features.openFiles[0]++;
        features.openFiles[1]++;
      } else if (whitePawns === 0) {
        features.halfOpenFiles[0]++;
      } else if (blackPawns === 0) {
        features.halfOpenFiles[1]++;
      }
    }

    return features;
  }
}
//////////////////////////////////
////////////////////////////////// ===================== NNUE IMPLEMENTATION =====================
class NNUE_HalfKAv2_Extended {
  constructor() {
    this.inputSize = 41024; // 64x64x10 + 256 (pawn structure features)
    this.hiddenSize = 256;
    this.outputSize = 1;
    
    // Network weights
    this.featureWeights = null;
    this.featureBias = null;
    this.hiddenWeights = null;
    this.hiddenBias = null;
    this.outputWeights = null;
    this.outputBias = 0;
    
    // Accumulator
    this.accumulator = new Int16Array(this.hiddenSize);
    this.kingSquare = [0, 0]; // [ourKing, theirKing]
    this.dirty = true;
    this.ready = false;
    
    // Default weights (small example, real weights would be much larger)
    this.defaultWeights = {
      featureWeights: new Int16Array(this.inputSize * this.hiddenSize).fill(0),
      featureBias: new Int16Array(this.hiddenSize).fill(0),
      hiddenWeights: new Int16Array(this.hiddenSize * 32).fill(0),
      hiddenBias: new Int16Array(32).fill(0),
      outputWeights: new Int16Array(32).fill(0),
      outputBias: 0
    };
  }

  async loadModel(url) {
    try {
      if (!url) {
        // Use default weights for testing
        this.loadFromObject(this.defaultWeights);
        this.ready = true;
        return;
      }

      const response = await fetch(url);
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      
      const buffer = await response.arrayBuffer();
      const data = new Int16Array(buffer);
      
      // Parse weights (adjust based on your NNUE file format)
      let ptr = 0;
      
      // Feature transformer weights (41024 x 256)
      this.featureWeights = data.subarray(ptr, ptr + this.inputSize * this.hiddenSize);
      ptr += this.inputSize * this.hiddenSize;
      
      // Feature transformer bias (256)
      this.featureBias = data.subarray(ptr, ptr + this.hiddenSize);
      ptr += this.hiddenSize;
      
      // Hidden layer weights (256 x 32)
      this.hiddenWeights = data.subarray(ptr, ptr + this.hiddenSize * 32);
      ptr += this.hiddenSize * 32;
      
      // Hidden layer bias (32)
      this.hiddenBias = data.subarray(ptr, ptr + 32);
      ptr += 32;
      
      // Output layer weights (32)
      this.outputWeights = data.subarray(ptr, ptr + 32);
      ptr += 32;
      
      // Output bias (1)
      this.outputBias = data[ptr];
      
      this.ready = true;
      console.log("NNUE model loaded successfully");
    } catch (e) {
      console.error("NNUE loading failed:", e);
      this.ready = false;
      throw e;
    }
  }

  loadFromObject(weights) {
    this.featureWeights = weights.featureWeights;
    this.featureBias = weights.featureBias;
    this.hiddenWeights = weights.hiddenWeights;
    this.hiddenBias = weights.hiddenBias;
    this.outputWeights = weights.outputWeights;
    this.outputBias = weights.outputBias;
  }

  evaluate(position) {
    if (!this.ready) return 0;
    
    this.updateAccumulator(position);
    
    // Hidden Layer (Clipped ReLU)
    let hidden = new Int32Array(32);
    for (let i = 0; i < 32; i++) {
      let sum = this.hiddenBias[i];
      for (let j = 0; j < this.hiddenSize; j++) {
        sum += this.accumulator[j] * this.hiddenWeights[j * 32 + i];
      }
      hidden[i] = Math.max(0, Math.min(127, sum >> 6)); // Clipped ReLU
    }
    
    // Output Layer
    let output = this.outputBias;
    for (let i = 0; i < 32; i++) {
      output += hidden[i] * this.outputWeights[i];
    }
    
    // Scale to centipawns and adjust for side
    return (output / 100.0) * (position.side === position.COLORS.WHITE ? 1 : -1);
  }

  updateAccumulator(position) {
    const ourKing = position.bitScanForward(
      position.bitboards[position.side * 6 + position.PIECE_TYPES.KING - 1]
    );
    const theirKing = position.bitScanForward(
      position.bitboards[(position.side ^ 1) * 6 + position.PIECE_TYPES.KING - 1]
    );
    
    // Only refresh if king moved or position is dirty
    if (ourKing !== this.kingSquare[0] || theirKing !== this.kingSquare[1] || this.dirty) {
      this.kingSquare = [ourKing, theirKing];
      this.dirty = false;
      
      // Reset accumulator to bias
      for (let i = 0; i < this.hiddenSize; i++) {
        this.accumulator[i] = this.featureBias[i];
      }
      
      // Add all piece features
      for (let pieceType = 0; pieceType < 10; pieceType++) {
        let bb;
        if (pieceType < 5) {
          // White pieces (PAWN, KNIGHT, BISHOP, ROOK, QUEEN)
          bb = position.bitboards[position.COLORS.WHITE * 6 + pieceType];
        } else if (pieceType < 10) {
          // Black pieces (PAWN, KNIGHT, BISHOP, ROOK, QUEEN)
          bb = position.bitboards[position.COLORS.BLACK * 6 + (pieceType - 5)];
        }
        
        while (bb) {
          const sq = position.bitScanForward(bb);
          bb &= bb - 1n;
          
          // Calculate feature index (HalfKAv2 layout)
          const featureIdx = (ourKing * 64 * 10) + (theirKing * 10) + pieceType * 64 + sq;
          
          // Add feature weights to accumulator
          for (let i = 0; i < this.hiddenSize; i++) {
            this.accumulator[i] += this.featureWeights[featureIdx * this.hiddenSize + i];
          }
        }
      }
      
      // Add pawn structure features (last 256 features)
      const pawnFeatures = position.pawnCache.getPawnStructureFeatures(position);
      const pawnFeatureOffset = 64 * 64 * 10;
      
      // Doubled pawns
      for (let i = 0; i < 2; i++) {
        const featureIdx = pawnFeatureOffset + i;
        for (let j = 0; j < this.hiddenSize; j++) {
          this.accumulator[j] += this.featureWeights[featureIdx * this.hiddenSize + j] * pawnFeatures.doubledPawns[i];
        }
      }
      
      // ... add other pawn structure features similarly
    }
  }

  // Helper function to convert weights between formats
  convertWeightsTo16Bit(sourceWeights) {
    const size = sourceWeights.length;
    const converted = new Int16Array(size);
    
    for (let i = 0; i < size; i++) {
      converted[i] = Math.max(-32768, Math.min(32767, Math.round(sourceWeights[i] * 127)));
    }
    
    return converted;
  }

  // For testing/demo purposes
  getSampleWeights() {
    return {
      featureWeights: this.convertWeightsTo16Bit(new Float32Array(this.inputSize * this.hiddenSize).fill(0.01)),
      featureBias: new Int16Array(this.hiddenSize).fill(10),
      hiddenWeights: this.convertWeightsTo16Bit(new Float32Array(this.hiddenSize * 32).fill(0.02)),
      hiddenBias: new Int16Array(32).fill(5),
      outputWeights: this.convertWeightsTo16Bit(new Float32Array(32).fill(0.5)),
      outputBias: 50
    };
  }
}

// ===================== NNUE WRAPPER =====================
class NNUEWrapper {
  constructor(engine) {
    this.engine = engine;
    this.nnue = new NNUE_HalfKAv2_Extended();
    this.ready = false;
  }

  async init() {
    try {
      await this.nnue.loadModel('nnue_halfkav2_ext.bin');
      this.ready = true;
    } catch (e) {
      console.error("NNUE initialization failed:", e);
      this.ready = false;
    }
    return this.ready;
  }

  evaluate(position) {
    if (!this.ready) return 0;
    
    // Scale NNUE evaluation based on game phase
    const phase = position.gamePhase() / 256;
    const nnueWeight = 0.2 + phase * 0.8; // NNUE gets stronger in endgame
    const classicalWeight = 1.5 - phase * 0.7; // Classical gets stronger in middlegame
    
    const nnueScore = this.nnue.evaluate(position);
    const classicalScore = this.engine.evaluator.classicalEval(position, phase);
    
    return (nnueScore * nnueWeight + classicalScore * classicalWeight) / 
           (nnueWeight + classicalWeight);
  }
}

//////////////////
// ===================== SYZYGY TABLEBASES IMPLEMENTATION =====================
 class SyzygyTablebases {
  constructor(maxPieces = 6) {
    this.maxPieces = maxPieces;
    this.ready = false;
    this.tbPath = '';
    this.tbCache = new Map();
    this.wdlCache = new Map();
    this.probeDepth = 0;
    this.probeLimit = 4; // Max depth to probe in the endgame
    
    // Metrics
    this.probeHits = 0;
    this.probeMisses = 0;
    this.saves = 0;
    
    // Compression scheme for positions
    this.pieceEncoding = {
      [this.PIECE_TYPES.PAWN]: 1,
      [this.PIECE_TYPES.KNIGHT]: 2,
      [this.PIECE_TYPES.BISHOP]: 3,
      [this.PIECE_TYPES.ROOK]: 4,
      [this.PIECE_TYPES.QUEEN]: 5,
      [this.PIECE_TYPES.KING]: 6
    };
  }

  async init(path = '') {
    this.tbPath = path;
    try {
      if (path) {
        // In a real implementation, this would load the tablebase files
        // For this example, we'll simulate successful loading
        await this.loadTablebases(path);
        this.ready = true;
        return true;
      }
      this.ready = false;
      return false;
    } catch (e) {
      console.error("Tablebase initialization failed:", e);
      this.ready = false;
      return false;
    }
  }

  // Simulated tablebase loading
  async loadTablebases(path) {
    // In a real implementation, this would:
    // 1. Scan the directory for .rtbw and .rtbz files
    // 2. Parse the headers and build an index
    // 3. Memory-map the files for fast access
    return new Promise((resolve) => {
      setTimeout(() => resolve(), 100); // Simulate async loading
    });
  }

  // Main probing function
  probe(position) {
    if (!this.ready || position.ply > this.probeLimit) return null;
    
    const pieceCount = this.countPieces(position);
    if (pieceCount > this.maxPieces) return null;
    
    const key = this.positionToKey(position);
    
    // Check cache first
    if (this.tbCache.has(key)) {
      this.probeHits++;
      return this.tbCache.get(key);
    }
    
    this.probeMisses++;
    
    // Simulated probing - in real implementation this would:
    // 1. Determine the correct tablebase file
    // 2. Look up the position
    // 3. Return the result if found
    const result = this.simulateProbe(position, pieceCount);
    
    if (result) {
      this.tbCache.set(key, result);
      this.saves++;
    }
    
    return result;
  }

  // Probe WDL (Win/Draw/Loss) statistics
  probeWDL(position) {
    if (!this.ready) return null;
    
    const key = this.positionToKey(position);
    if (this.wdlCache.has(key)) {
      return this.wdlCache.get(key);
    }
    
    // Simulated WDL probe
    const wdl = this.simulateWDLProbe(position);
    if (wdl) {
      this.wdlCache.set(key, wdl);
    }
    
    return wdl;
  }

  // Count total pieces on the board
  countPieces(position) {
    let count = 0;
    for (let i = 0; i < 12; i++) {
      count += position.popCount(position.bitboards[i]);
    }
    return count;
  }

  // Convert position to a cache key
  positionToKey(position) {
    let key = position.side === position.COLORS.WHITE ? 'w' : 'b';
    
    // Add pieces in a consistent order
    for (let color = 0; color < 2; color++) {
      for (let pieceType = 0; pieceType < 6; pieceType++) {
        let bb = position.bitboards[color * 6 + pieceType];
        while (bb) {
          const sq = position.bitScanForward(bb);
          bb &= bb - 1n;
          key += `${color}${pieceType}${sq}:`;
        }
      }
    }
    
    // Add castling rights and ep square
    key += `c${position.castling}e${position.epSquare}`;
    return key;
  }

  // Simulate a tablebase probe (for demonstration)
  simulateProbe(position, pieceCount) {
    // In a real implementation, this would access the actual tablebase files
    // Here we return simulated results for known endgames
    
    // KQ vs K (white wins)
    if (pieceCount === 3) {
      const whiteQueen = position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.QUEEN - 1];
      if (whiteQueen) {
        return {
          success: true,
          bestMove: this.findMateInOne(position),
          score: position.MATE_VALUE - position.ply,
          wdl: 2, // Win
          dtz: 10 // Distance to zero
        };
      }
    }
    
    // KR vs K (white wins)
    if (pieceCount === 3) {
      const whiteRook = position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.ROOK - 1];
      if (whiteRook) {
        return {
          success: true,
          bestMove: this.findKRKMove(position),
          score: position.MATE_VALUE - position.ply - 10,
          wdl: 2, // Win
          dtz: 20 // Distance to zero
        };
      }
    }
    
    // KP vs K (depends on position)
    if (pieceCount === 3) {
      const whitePawn = position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.PAWN - 1];
      if (whitePawn) {
        return this.analyzeKPK(position);
      }
    }
    
    return null;
  }

  // Simulate WDL probe
  simulateWDLProbe(position) {
    const pieceCount = this.countPieces(position);
    if (pieceCount > 5) return null;
    
    // Simulate some common endgame results
    if (pieceCount === 2) {
      return 0; // KVK is always a draw
    }
    
    // KQK is win
    if (pieceCount === 3 && 
        position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.QUEEN - 1]) {
      return 2;
    }
    
    // KRK is win
    if (pieceCount === 3 && 
        position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.ROOK - 1]) {
      return 2;
    }
    
    // KPK depends on position
    if (pieceCount === 3 && 
        position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.PAWN - 1]) {
      return this.analyzeKPKWDL(position);
    }
    
    return null;
  }

  // Find a mate in one move (for KQ vs K)
  findMateInOne(position) {
    const moves = position.generateMoves();
    for (const move of moves) {
      const undo = position.makeMove(move);
      if (position.isInCheckmate()) {
        position.undoMove(move, undo);
        return move;
      }
      position.undoMove(move, undo);
    }
    return moves[0]; // Fallback
  }

  // Find a good KRK move
  findKRKMove(position) {
    const moves = position.generateMoves();
    
    // Prefer checks and king approaches
    const theirKing = position.bitScanForward(
      position.bitboards[position.side ^ 1 * 6 + position.PIECE_TYPES.KING - 1]
    );
    
    let bestMove = moves[0];
    let bestScore = -Infinity;
    
    for (const move of moves) {
      let score = 0;
      
      // Checking moves are good
      const undo = position.makeMove(move);
      if (position.isInCheck()) {
        score += 100;
      }
      position.undoMove(move, undo);
      
      // Rook moves that limit the enemy king
      if (move.piece === position.PIECE_TYPES.ROOK) {
        const toFile = move.to % 8;
        const toRank = Math.floor(move.to / 8);
        const theirKingFile = theirKing % 8;
        const theirKingRank = Math.floor(theirKing / 8);
        
        // Prefer cutting off the king
        if (toFile === theirKingFile || toRank === theirKingRank) {
          score += 50;
        }
      }
      
      // King moves that approach the enemy king
      if (move.piece === position.PIECE_TYPES.KING) {
        const distBefore = this.kingDistance(
          move.from, 
          theirKing
        );
        const distAfter = this.kingDistance(
          move.to,
          theirKing
        );
        score += (distBefore - distAfter) * 20;
      }
      
      if (score > bestScore) {
        bestScore = score;
        bestMove = move;
      }
    }
    
    return bestMove;
  }

  // Calculate distance between two squares
  kingDistance(sq1, sq2) {
    const file1 = sq1 % 8;
    const rank1 = Math.floor(sq1 / 8);
    const file2 = sq2 % 8;
    const rank2 = Math.floor(sq2 / 8);
    
    return Math.max(Math.abs(file1 - file2), Math.abs(rank1 - rank2));
  }

  // Analyze KPK endgame
  analyzeKPK(position) {
    const whitePawn = position.bitScanForward(
      position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.PAWN - 1]
    );
    const whiteKing = position.bitScanForward(
      position.bitboards[position.COLORS.WHITE * 6 + position.PIECE_TYPES.KING - 1]
    );
    const blackKing = position.bitScanForward(
      position.bitboards[position.COLORS.BLACK * 6 + position.PIECE_TYPES.KING - 1]
    );
    
    if (!whitePawn || !whiteKing || !blackKing) return null;
    
    const pawnFile = whitePawn % 8;
    const pawnRank = Math.floor(whitePawn / 8);
    
    // Basic KPK rules
    const isPassed = !this.isPawnStoppable(position, whitePawn);
    const canPromote = isPassed && this.canKingSupportPromotion(position, whiteKing, whitePawn);
    
    if (canPromote) {
      // Find the promotion push
      const moves = position.generateMoves();
      for (const move of moves) {
        if (move.piece === position.PIECE_TYPES.PAWN && 
            move.flags === position.MOVE_FLAGS.PROMOTION) {
          return {
            success: true,
            bestMove: move,
            score: position.MATE_VALUE - position.ply - (7 - pawnRank),
            wdl: 2,
            dtz: (7 - pawnRank) * 2
          };
        }
      }
    }
    
    // Return null if not a clear win
    return null;
  }

  // Check if pawn can be stopped
  isPawnStoppable(position, pawnSq) {
    const pawnRank = Math.floor(pawnSq / 8);
    const pawnFile = pawnSq % 8;
    const blackKing = position.bitScanForward(
      position.bitboards[position.COLORS.BLACK * 6 + position.PIECE_TYPES.KING - 1]
    );
    
    const blackKingFile = blackKing % 8;
    const blackKingRank = Math.floor(blackKing / 8);
    
    // Can the black king catch the pawn?
    const promotionDist = 7 - pawnRank;
    const kingDist = Math.max(
      Math.abs(blackKingFile - pawnFile),
      Math.abs(blackKingRank - (pawnRank + 1))
    );
    
    return kingDist <= promotionDist;
  }

  // Check if king can support pawn promotion
  canKingSupportPromotion(position, kingSq, pawnSq) {
    const pawnRank = Math.floor(pawnSq / 8);
    const kingDist = this.kingDistance(kingSq, pawnSq + 8);
    
    return kingDist <= (7 - pawnRank);
  }

  // Analyze KPK WDL
  analyzeKPKWDL(position) {
    const result = this.analyzeKPK(position);
    return result ? result.wdl : 0;
  }

  // Clear caches
  clearCache() {
    this.tbCache.clear();
    this.wdlCache.clear();
    this.probeHits = 0;
    this.probeMisses = 0;
    this.saves = 0;
  }

  // Get statistics
  getStats() {
    return {
      ready: this.ready,
      maxPieces: this.maxPieces,
      cacheSize: this.tbCache.size,
      wdlCacheSize: this.wdlCache.size,
      probeHits: this.probeHits,
      probeMisses: this.probeMisses,
      hitRate: this.probeHits / (this.probeHits + this.probeMisses) || 0,
      saves: this.saves
    };
  }
}



//////////////////
// ===================== OPENING BOOK IMPLEMENTATION =====================
 class OpeningBook {
  constructor() {
    this.book = new Map();
    this.ready = false;
    this.maxDepth = 40; // Max ply to use book moves
    this.contempt = 0; // Preference for draws (0 = neutral, + = avoid, - = prefer)
    this.weightedRandom = true; // Use weighted random selection
    this.stats = {
      hits: 0,
      misses: 0,
      weightedChoices: 0,
      fallbacks: 0
    };
  }

  async load(url) {
    try {
      if (typeof url === 'string') {
        // Load from external file
        const response = await fetch(url);
        if (!response.ok) throw new Error(`HTTP ${response.status}`);
        const data = await response.json();
        this.parseBookData(data);
      } else if (url instanceof Map) {
        // Load from existing Map
        this.book = new Map(url);
      } else if (typeof url === 'object') {
        // Load from object
        this.parseBookData(url);
      } else {
        // Initialize with basic opening moves
        this.initDefaultBook();
      }
      
      this.ready = true;
      return true;
    } catch (e) {
      console.error("Opening book loading failed:", e);
      this.ready = false;
      return false;
    }
  }

  parseBookData(data) {
    if (Array.isArray(data)) {
      // Array format: [{fen: "", moves: [{move: "", weight: 1}, ...]}, ...]
      data.forEach(entry => {
        this.book.set(entry.fen, entry.moves);
      });
    } else if (typeof data === 'object') {
      // Object format: {fen: {move: weight, ...}, ...}
      Object.entries(data).forEach(([fen, moves]) => {
        const moveList = Object.entries(moves).map(([move, weight]) => ({
          move,
          weight: typeof weight === 'number' ? weight : 1
        }));
        this.book.set(fen, moveList);
      });
    }
  }

  initDefaultBook() {
    // Basic opening moves for demonstration
    const basicOpenings = {
      // Standard opening positions
      "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1": [
        {move: "e2e4", weight: 60},  // King's pawn
        {move: "d2d4", weight: 30},  // Queen's pawn
        {move: "g1f3", weight: 5},   // Reti
        {move: "c2c4", weight: 5}    // English
      ],
      // After 1.e4
      "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1": [
        {move: "e7e5", weight: 50},  // Open game
        {move: "c7c5", weight: 30},  // Sicilian
        {move: "e7e6", weight: 10},  // French
        {move: "c7c6", weight: 10}   // Caro-Kann
      ],
      // After 1.e4 e5
      "rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2": [
        {move: "g1f3", weight: 40},  // Ruy Lopez
        {move: "f1c4", weight: 30},  // Italian
        {move: "f2f4", weight: 15},  // King's Gambit
        {move: "d2d4", weight: 15}   // Center Game
      ]
    };
    
    this.parseBookData(basicOpenings);
  }

  getMove(fen, options = {}) {
    if (!this.ready || !this.book.has(fen)) {
      this.stats.misses++;
      return null;
    }
    
    this.stats.hits++;
    const moves = this.book.get(fen);
    const filteredMoves = this.filterMoves(moves, options);
    
    if (filteredMoves.length === 0) {
      this.stats.fallbacks++;
      return null;
    }
    
    return this.weightedRandom 
      ? this.selectWeightedMove(filteredMoves)
      : this.selectBestMove(filteredMoves);
  }

  filterMoves(moves, options) {
    // Apply various filters based on options
    let result = [...moves];
    
    // Filter by minimum weight if specified
    if (typeof options.minWeight === 'number') {
      result = result.filter(m => m.weight >= options.minWeight);
    }
    
    // Filter out draws if contempt is positive
    if (this.contempt > 0 && options.wdl) {
      result = result.filter(m => m.wdl !== 0);
    }
    
    // Filter by player preference if specified
    if (options.preferredMoves) {
      const preferred = new Set(options.preferredMoves);
      result = result.filter(m => preferred.has(m.move));
    }
    
    return result;
  }

  selectWeightedMove(moves) {
    // Calculate total weight
    const totalWeight = moves.reduce((sum, m) => sum + m.weight, 0);
    const random = Math.random() * totalWeight;
    
    // Select move based on weighted probability
    let cumulative = 0;
    for (const move of moves) {
      cumulative += move.weight;
      if (random <= cumulative) {
        this.stats.weightedChoices++;
        return move.move;
      }
    }
    
    // Fallback to last move (shouldn't happen)
    return moves[moves.length - 1].move;
  }

  selectBestMove(moves) {
    // Simply select the move with highest weight
    return moves.reduce((best, current) => 
      current.weight > best.weight ? current : best
    ).move;
  }

  addMove(fen, move, weight = 1, wdl = null) {
    if (!this.book.has(fen)) {
      this.book.set(fen, []);
    }
    
    const moves = this.book.get(fen);
    const existing = moves.find(m => m.move === move);
    
    if (existing) {
      existing.weight = weight;
      if (wdl !== null) existing.wdl = wdl;
    } else {
      moves.push({move, weight, wdl});
    }
  }

  removeMove(fen, move) {
    if (!this.book.has(fen)) return false;
    
    const moves = this.book.get(fen);
    const index = moves.findIndex(m => m.move === move);
    
    if (index >= 0) {
      moves.splice(index, 1);
      if (moves.length === 0) this.book.delete(fen);
      return true;
    }
    
    return false;
  }

  adjustWeights(fen, adjustmentFn) {
    if (!this.book.has(fen)) return;
    
    const moves = this.book.get(fen);
    moves.forEach(move => {
      move.weight = adjustmentFn(move.weight, move);
    });
  }

  getStats() {
    return {
      ...this.stats,
      size: this.book.size,
      ready: this.ready,
      weightedRandom: this.weightedRandom,
      maxDepth: this.maxDepth,
      contempt: this.contempt
    };
  }

  clearStats() {
    this.stats = {
      hits: 0,
      misses: 0,
      weightedChoices: 0,
      fallbacks: 0
    };
  }

  // Advanced book building and maintenance
  buildFromGames(games, options = {}) {
    const minGames = options.minGames || 3;
    const minWinRate = options.minWinRate || 0.4;
    const maxPly = options.maxPly || this.maxDepth;
    
    const positionCounts = new Map();
    
    games.forEach(game => {
      const position = new Position(); // Your engine's position class
      position.setPosition("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
      
      for (let i = 0; i < Math.min(game.moves.length, maxPly); i++) {
        const move = game.moves[i];
        const fen = position.getFEN();
        
        if (!positionCounts.has(fen)) {
          positionCounts.set(fen, new Map());
        }
        
        const moveCounts = positionCounts.get(fen);
        if (!moveCounts.has(move)) {
          moveCounts.set(move, {count: 0, results: []});
        }
        
        const record = moveCounts.get(move);
        record.count++;
        record.results.push(game.result);
        
        position.makeMove(position.parseUCIMove(move));
      }
    });
    
    // Convert counts to book entries
    positionCounts.forEach((moveCounts, fen) => {
      const moves = [];
      
      moveCounts.forEach((stats, move) => {
        if (stats.count >= minGames) {
          const winRate = stats.results.filter(r => r === '1-0').length / stats.count;
          const lossRate = stats.results.filter(r => r === '0-1').length / stats.count;
          const drawRate = 1 - winRate - lossRate;
          
          if (winRate >= minWinRate || lossRate >= minWinRate) {
            let weight = stats.count;
            let wdl = winRate > lossRate ? 1 : -1;
            
            // Adjust for contempt
            if (this.contempt > 0 && drawRate > 0.5) {
              weight *= 0.5;
            }
            
            moves.push({move, weight, wdl});
          }
        }
      });
      
      if (moves.length > 0) {
        this.book.set(fen, moves);
      }
    });
  }

  // Convert to compact format for saving
  toJSON() {
    const obj = {};
    this.book.forEach((moves, fen) => {
      const moveObj = {};
      moves.forEach(m => {
        moveObj[m.move] = m.weight;
        if (m.wdl !== undefined) moveObj[`${m.move}_wdl`] = m.wdl;
      });
      obj[fen] = moveObj;
    });
    return obj;
  }

  // Merge another book into this one
  merge(otherBook, options = {}) {
    const mergeFn = options.preferNew 
      ? (newWeight, oldWeight) => newWeight
      : (newWeight, oldWeight) => newWeight + oldWeight;
    
    otherBook.book.forEach((moves, fen) => {
      if (!this.book.has(fen)) {
        this.book.set(fen, moves.map(m => ({...m})));
      } else {
        const existingMoves = this.book.get(fen);
        moves.forEach(newMove => {
          const existing = existingMoves.find(m => m.move === newMove.move);
          if (existing) {
            existing.weight = mergeFn(newMove.weight, existing.weight);
            if (newMove.wdl !== undefined) {
              existing.wdl = newMove.wdl;
            }
          } else {
            existingMoves.push({...newMove});
          }
        });
      }
    });
  }

  // Prune less important moves
  prune(options = {}) {
    const minWeight = options.minWeight || 1;
    const maxMoves = options.maxMoves || 5;
    const minWinRate = options.minWinRate || 0.3;
    
    this.book.forEach((moves, fen) => {
      // Filter by weight and win rate
      let filtered = moves.filter(m => 
        m.weight >= minWeight && 
        (!m.wdl || Math.abs(m.wdl) >= minWinRate)
      );
      
      // Limit number of moves
      if (filtered.length > maxMoves) {
        filtered.sort((a, b) => b.weight - a.weight);
        filtered = filtered.slice(0, maxMoves);
      }
      
      if (filtered.length === 0) {
        this.book.delete(fen);
      } else {
        this.book.set(fen, filtered);
      }
    });
  }
}


// ===================== CHESS.JS-LIKE API =====================
class Chess {
    constructor(fen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1') {
        this.engine = new SKY5LChess();
        this.engine.setPosition(fen);
        this.moveHistory = [];
        this.gameOver = false;
        this.result = null;
    }

    // Reset the game to initial position
    reset() {
        this.engine.setPosition('rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1');
        this.moveHistory = [];
        this.gameOver = false;
        this.result = null;
        return this;
    }

    // Load a FEN string
    load(fen) {
        this.engine.setPosition(fen);
        this.moveHistory = [];
        this.gameOver = false;
        this.result = null;
        return this;
    }

    // Get current FEN string
    fen() {
        return this.engine.getFEN();
    }

    // Get the current side to move ('w' or 'b')
    turn() {
        return this.engine.side === this.engine.COLORS.WHITE ? 'w' : 'b';
    }

    // Make a move from algebraic notation (e.g. 'e4', 'Nf3', 'a8=Q')
    move(move) {
        if (this.gameOver) return null;
        
        const moves = this.engine.generateMoves();
        const moveObj = this.findMoveFromNotation(move, moves);
        
        if (!moveObj) return null;
        
        const undo = this.engine.makeMove(moveObj);
        this.moveHistory.push({
            move: moveObj,
            fen: this.fen(),
            undo: undo
        });
        
        this.checkGameEnd();
        return this.convertMoveToOutput(moveObj);
    }

    // Undo the last move
    undo() {
        if (this.moveHistory.length === 0) return null;
        
        const lastMove = this.moveHistory.pop();
        this.engine.undoMove(lastMove.move, lastMove.undo);
        this.gameOver = false;
        this.result = null;
        return this.convertMoveToOutput(lastMove.move);
    }

    // Get all valid moves for current position
    moves(options = {}) {
        const moves = this.engine.generateMoves();
        
        if (options.verbose) {
            return moves.map(move => this.convertMoveToOutput(move, true));
        }
        
        return moves.map(move => this.moveToAlgebraic(move));
    }

    // Check if the game is over
    isGameOver() {
        this.checkGameEnd();
        return this.gameOver;
    }

    // Get the game result ('1-0', '0-1', '1/2-1/2', or null if game continues)
    result() {
        this.checkGameEnd();
        return this.result;
    }

    // Get the board representation as a 2D array
    board() {
        const board = Array(8).fill().map(() => Array(8).fill(null));
        
        for (let pieceType = 0; pieceType < 12; pieceType++) {
            let bb = this.engine.bitboards[pieceType];
            while (bb) {
                const sq = this.engine.bitScanForward(bb);
                bb &= bb - 1n;
                
                const row = 7 - Math.floor(sq / 8);
                const col = sq % 8;
                const color = pieceType < 6 ? 'w' : 'b';
                const type = this.pieceTypeToSymbol(pieceType % 6 + 1);
                
                board[row][col] = { type, color, square: this.indexToSquare(sq) };
            }
        }
        
        return board;
    }

    // Get the piece on a square (e.g. 'e4')
    get(square) {
        const index = this.squareToIndex(square);
        if (index === -1) return null;
        
        for (let pieceType = 0; pieceType < 12; pieceType++) {
            if (this.engine.bitboards[pieceType] & (1n << BigInt(index))) {
                const color = pieceType < 6 ? 'w' : 'b';
                const type = this.pieceTypeToSymbol(pieceType % 6 + 1);
                return { type, color, square };
            }
        }
        
        return null;
    }

    // Check if a square is attacked by the given color
    isAttacked(square, color) {
        const index = this.squareToIndex(square);
        if (index === -1) return false;
        
        return this.engine.isSquareAttacked(
            index, 
            color === 'w' ? this.engine.COLORS.WHITE : this.engine.COLORS.BLACK
        );
    }

    // Check if the current side is in check
    isCheck() {
        return this.engine.isInCheck();
    }

    // Check if the current position is a checkmate
    isCheckmate() {
        return this.isGameOver() && this.engine.isInCheck() && 
               this.engine.generateMoves().length === 0;
    }

    // Check if the current position is a draw
    isDraw() {
        return this.isGameOver() && !this.isCheckmate() && this.result === '1/2-1/2';
    }

    // Get the current move number
    moveNumber() {
        return this.engine.fullmoveNumber;
    }

    // Get the history of moves in SAN format
    history(options = {}) {
        if (options.verbose) {
            return this.moveHistory.map(entry => this.convertMoveToOutput(entry.move, true));
        }
        return this.moveHistory.map(entry => this.moveToAlgebraic(entry.move));
    }

    // ===== Helper Methods =====
    checkGameEnd() {
        if (this.gameOver) return;
        
        if (this.engine.isGameOver()) {
            this.gameOver = true;
            const result = this.engine.getGameResult();
            this.result = result === 0.5 ? '1/2-1/2' : 
                         result === this.engine.COLORS.WHITE ? '1-0' : '0-1';
        }
    }

    findMoveFromNotation(notation, moves) {
        const cleanNotation = notation.replace(/[+#]?[?!]*$/, '');
        
        // Try exact match first
        for (const move of moves) {
            if (this.moveToAlgebraic(move) === cleanNotation) {
                return move;
            }
        }
        
        // Try more flexible matching
        const from = this.squareToIndex(cleanNotation.substring(0, 2));
        const to = this.squareToIndex(cleanNotation.substring(2, 4));
        
        if (from === -1 || to === -1) return null;
        
        // Check for promotion
        let promotion = null;
        if (cleanNotation.length === 5) {
            const promo = cleanNotation[4].toLowerCase();
            const promoPieces = {q: this.engine.QUEEN, r: this.engine.ROOK, 
                                b: this.engine.BISHOP, n: this.engine.KNIGHT};
            promotion = promoPieces[promo];
        }
        
        // Find matching move
        for (const move of moves) {
            if (move.from === from && move.to === to) {
                if (move.flags === this.engine.FLAGS.PROMOTION) {
                    if (promotion && move.promotion === promotion) {
                        return move;
                    }
                } else if (!promotion) {
                    return move;
                }
            }
        }
        
        return null;
    }

    moveToAlgebraic(move) {
        const files = 'abcdefgh';
        const fromFile = files[move.from % 8];
        const fromRank = 8 - Math.floor(move.from / 8);
        const toFile = files[move.to % 8];
        const toRank = 8 - Math.floor(move.to / 8);
        
        let notation = fromFile + fromRank + toFile + toRank;
        
        if (move.flags === this.engine.FLAGS.PROMOTION) {
            const promo = {[this.engine.QUEEN]: 'q', [this.engine.ROOK]: 'r',
                          [this.engine.BISHOP]: 'b', [this.engine.KNIGHT]: 'n'};
            notation += promo[move.promotion];
        }
        
        return notation;
    }

    convertMoveToOutput(move, verbose = false) {
        const files = 'abcdefgh';
        const from = files[move.from % 8] + (8 - Math.floor(move.from / 8));
        const to = files[move.to % 8] + (8 - Math.floor(move.to / 8));
        const color = this.engine.side === this.engine.COLORS.WHITE ? 'w' : 'b';
        const piece = this.pieceTypeToSymbol(move.piece);
        
        if (!verbose) {
            return this.moveToAlgebraic(move);
        }
        
        const output = {
            color,
            from,
            to,
            piece,
            flags: '',
            san: this.moveToAlgebraic(move)
        };
        
        if (move.flags === this.engine.FLAGS.CAPTURE) {
            output.captured = this.pieceTypeToSymbol(move.captured);
            output.flags += 'c';
        }
        if (move.flags === this.engine.FLAGS.PROMOTION) {
            output.promotion = this.pieceTypeToSymbol(move.promotion);
            output.flags += 'p';
        }
        if (move.flags === this.engine.FLAGS.ENPASSANT) {
            output.captured = 'p';
            output.flags += 'e';
        }
        if (move.flags === this.engine.FLAGS.CASTLING) {
            output.flags += 'k';
        }
        
        return output;
    }

    pieceTypeToSymbol(pieceType) {
        const symbols = ['', 'p', 'n', 'b', 'r', 'q', 'k'];
        return symbols[pieceType];
    }

    squareToIndex(square) {
        if (square.length !== 2) return -1;
        const file = square.charCodeAt(0) - 'a'.charCodeAt(0);
        const rank = 8 - parseInt(square[1]);
        if (file < 0 || file > 7 || rank < 0 || rank > 7) return -1;
        return rank * 8 + file;
    }

    indexToSquare(index) {
        const files = 'abcdefgh';
        const file = files[index % 8];
        const rank = 8 - Math.floor(index / 8);
        return file + rank;
    }
}

//////////////
///////////////////////////

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

class UCIInterface {
    constructor(engine) {
        this.engine = engine;
        this.isReady = false;
        this.isSearching = false;
        this.debugMode = false;

        // Initialize IO handlers (Node.js or Browser/Worker)
        if (typeof process !== 'undefined') {
            // Node.js
            process.stdin.setEncoding('utf8');
            process.stdin.on('data', (data) => this.processInput(data));
            this.send = (msg) => process.stdout.write(msg + '\n');
        } else if (typeof self !== 'undefined') {
            // Web Worker
            self.onmessage = (e) => this.processInput(e.data);
            this.send = (msg) => self.postMessage({ type: 'uci', message: msg });
        } else {
            // Browser (if needed)
            console.warn("UCI running in browser without Worker support");
            this.send = (msg) => console.log("UCI>", msg);
        }
    }

    /**
     * Process UCI commands with error handling
     * @param {string} input - Raw UCI command(s)
     */
    async processInput(input) {
        const commands = input.trim().split('\n');
        
        for (const rawCommand of commands) {
            const command = rawCommand.trim();
            if (!command) continue;

            try {
                const response = await this.handleCommand(command);
                if (response) this.send(response);
            } catch (error) {
                this.send(`error ${error.message}`);
                if (this.debugMode) console.error(error);
            }
        }
    }

    /**
     * Handle a single UCI command
     * @param {string} command - UCI command
     * @returns {Promise<string>} - Response (if any)
     */
    async handleCommand(command) {
        const parts = command.split(/\s+/);
        const cmd = parts[0].toLowerCase();

        switch (cmd) {
            case 'uci':
                return this.handleUCI();
            case 'isready':
                return this.handleIsReady();
            case 'ucinewgame':
                return this.handleUCINewGame();
            case 'position':
                return this.handlePosition(parts.slice(1));
            case 'go':
                return this.handleGo(parts.slice(1));
            case 'stop':
                return this.handleStop();
            case 'quit':
                return this.handleQuit();
            case 'debug':
                return this.handleDebug(parts[1]);
            case 'setoption':
                return this.handleSetOption(parts.slice(1));
            case 'ponderhit':
                return this.handlePonderHit();
            case 'register':
                return this.handleRegister();
            default:
                throw new Error(`Unknown command: ${cmd}`);
        }
    }

    // ===================== UCI COMMAND HANDLERS =====================

    handleUCI() {
        return [
            'id name SKY5L Chess Engine',
            'id author Your Name',
            'option name Hash type spin default 128 min 1 max 2048',
            'option name Threads type spin default 1 min 1 max 128',
            'option name Contempt type spin default 0 min -100 max 100',
            'option name SyzygyPath type string default <empty>',
            'option name Ponder type check default false',
            'option name MultiPV type spin default 1 min 1 max 10',
            'uciok'
        ].join('\n');
    }

    async handleIsReady() {
        if (!this.isReady) {
            await this.engine.init();
            this.isReady = true;
        }
        return 'readyok';
    }

    handleUCINewGame() {
        this.engine.resetGame();
        return '';
    }

    handlePosition(parts) {
        let idx = 0;
        let fen;
        let moves = [];

        // Parse FEN or startpos
        if (parts[idx] === 'startpos') {
            fen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
            idx++;
        } else if (parts[idx] === 'fen') {
            fen = parts.slice(idx + 1, idx + 7).join(' ');
            idx += 7;
        } else {
            throw new Error('Invalid position command');
        }

        // Parse moves (if any)
        if (parts[idx] === 'moves') {
            moves = parts.slice(idx + 1);
        }

        // Apply position
        this.engine.setPosition(fen);

        // Apply moves
        for (const moveUCI of moves) {
            const move = this.engine.parseUCIMove(moveUCI);
            if (!move) throw new Error(`Invalid move: ${moveUCI}`);
            this.engine.makeMove(move);
        }

        return '';
    }

    async handleGo(parts) {
        if (this.isSearching) {
            throw new Error('Search already in progress');
        }

        const limits = {};
        for (let i = 0; i < parts.length; i++) {
            switch (parts[i]) {
                case 'wtime': limits.wtime = parseInt(parts[++i]); break;
                case 'btime': limits.btime = parseInt(parts[++i]); break;
                case 'winc': limits.winc = parseInt(parts[++i]); break;
                case 'binc': limits.binc = parseInt(parts[++i]); break;
                case 'movestogo': limits.movestogo = parseInt(parts[++i]); break;
                case 'depth': limits.depth = parseInt(parts[++i]); break;
                case 'nodes': limits.nodes = parseInt(parts[++i]); break;
                case 'movetime': limits.movetime = parseInt(parts[++i]); break;
                case 'infinite': limits.infinite = true; break;
                case 'ponder': limits.ponder = true; break;
            }
        }

        this.isSearching = true;
        const bestMove = await this.engine.getBestMove(this.engine, limits);
        this.isSearching = false;

        return `bestmove ${this.engine.moveToUCI(bestMove)}${limits.ponder ? ' ponder' : ''}`;
    }

    handleStop() {
        this.engine.stopSearch = true;
        this.isSearching = false;
        return '';
    }

    handleQuit() {
        this.engine.stopSearch = true;
        if (typeof process !== 'undefined') process.exit(0);
        return '';
    }

    handleDebug(mode) {
        this.debugMode = (mode === 'on');
        return '';
    }

    handleSetOption(parts) {
        if (parts.length < 2 || parts[0] !== 'name') {
            throw new Error('Invalid setoption syntax');
        }

        const nameEnd = parts.indexOf('value');
        const name = parts.slice(1, nameEnd > 0 ? nameEnd : undefined).join(' ');
        const value = nameEnd > 0 ? parts.slice(nameEnd + 1).join(' ') : null;

        switch (name.toLowerCase()) {
            case 'hash':
                this.engine.initTranspositionTable(parseInt(value));
                break;
            case 'threads':
                this.engine.search.threads = parseInt(value);
                break;
            case 'contempt':
                this.engine.contempt = parseInt(value);
                break;
            case 'syzygypath':
                this.engine.syzygy.init(value);
                break;
            default:
                if (this.debugMode) console.warn(`Unknown option: ${name}`);
        }

        return '';
    }

    handlePonderHit() {
        // Handle ponderhit if pondering is implemented
        return '';
    }

    handleRegister() {
        // Handle engine registration (if needed)
        return '';
    }
}
///////////////////////
/**
 * Utility functions for the chess engine
 */

export function bitScanForward(bb) {
  if (bb === 0n) return -1;
  return 63 - Math.clz32(Number(bb & -bb));
}

export function popCount(bb) {
  let count = 0;
  while (bb) {
    count++;
    bb &= bb - 1n;
  }
  return count;
}

export function getFile(square) {
  return square % 8;
}

export function getRank(square) {
  return Math.floor(square / 8);
}

export function squareToIndex(square) {
  if (square.length !== 2) return -1;
  const file = square.charCodeAt(0) - 'a'.charCodeAt(0);
  const rank = 8 - parseInt(square[1]);
  if (file < 0 || file > 7 || rank < 0 || rank > 7) return -1;
  return rank * 8 + file;
}

export function indexToSquare(index) {
  const files = 'abcdefgh';
  const file = files[index % 8];
  const rank = 8 - Math.floor(index / 8);
  return file + rank;
}

export function pieceTypeToSymbol(pieceType) {
  const symbols = ['', 'p', 'n', 'b', 'r', 'q', 'k'];
  return symbols[pieceType];
}

export function charToPiece(c, colors) {
  switch (c.toLowerCase()) {
    case 'p': return (c === 'p' ? colors.BLACK : colors.WHITE) * 6 + 1;
    case 'n': return (c === 'n' ? colors.BLACK : colors.WHITE) * 6 + 2;
    case 'b': return (c === 'b' ? colors.BLACK : colors.WHITE) * 6 + 3;
    case 'r': return (c === 'r' ? colors.BLACK : colors.WHITE) * 6 + 4;
    case 'q': return (c === 'q' ? colors.BLACK : colors.WHITE) * 6 + 5;
    case 'k': return (c === 'k' ? colors.BLACK : colors.WHITE) * 6 + 6;
    default: return -1;
  }
}

export function cloneObject(obj) {
  return JSON.parse(JSON.stringify(obj));
}

export function rand64() {
  const buf = new Uint32Array(2);
  crypto.getRandomValues(buf);
  return (BigInt(buf[0]) << 32n) | BigInt(buf[1]);
}


/**
 * Performance testing (perft) for move generation
 */

export class Perft {
  constructor(engine) {
    this.engine = engine;
  }

  async run(depth, fen = null) {
    const position = fen ? this.engine.createGame(fen) : this.engine.createGame();
    return this._perft(position, depth);
  }

  async _perft(position, depth) {
    if (depth === 0) return 1;

    const moves = position.generateMoves();
    let nodes = 0;

    for (const move of moves) {
      const undo = position.makeMove(move);
      nodes += await this._perft(position, depth - 1);
      position.undoMove(move, undo);
    }

    return nodes;
  }

  async runWithDetails(depth, fen = null) {
    const position = fen ? this.engine.createGame(fen) : this.engine.createGame();
    const moves = position.generateMoves();
    const results = [];

    for (const move of moves) {
      const undo = position.makeMove(move);
      const nodes = await this._perft(position, depth - 1);
      position.undoMove(move, undo);

      results.push({
        move: this.engine.moveToAlgebraic(move),
        nodes
      });
    }

    const total = results.reduce((sum, r) => sum + r.nodes, 0);
    return { total, breakdown: results };
  }
}

/**
 * Debugging utilities for the chess engine
 */

export class Debug {
  static printBitboard(bb, title = '') {
    console.log(title);
    for (let rank = 7; rank >= 0; rank--) {
      let line = '';
      for (let file = 0; file < 8; file++) {
        const square = rank * 8 + file;
        line += (bb & (1n << BigInt(square))) ? '1 ' : '0 ';
      }
      console.log(line);
    }
    console.log('\n');
  }

  static printBoard(position) {
    const board = Array(8).fill().map(() => Array(8).fill('.'));

    for (let pieceType = 0; pieceType < 12; pieceType++) {
      let bb = position.bitboards[pieceType];
      while (bb) {
        const sq = position.bitScanForward(bb);
        bb &= bb - 1n;
        
        const row = 7 - Math.floor(sq / 8);
        const col = sq % 8;
        const color = pieceType < 6 ? 'w' : 'b';
        const type = position.pieceTypeToSymbol(pieceType % 6 + 1);
        
        board[row][col] = color === 'w' ? type.toUpperCase() : type.toLowerCase();
      }
    }

    console.log('  a b c d e f g h');
    console.log('  ----------------');
    for (let i = 0; i < 8; i++) {
      console.log(`${8 - i}|${board[i].join(' ')}`);
    }
    console.log('\n');
  }

  static logSearchInfo(depth, score, pv, nodes, time) {
    const nps = Math.floor(nodes / (time / 1000));
    console.log(
      `info depth ${depth} ` +
      `score cp ${Math.round(score)} ` +
      `nodes ${nodes} ` +
      `nps ${nps} ` +
      `time ${time}ms ` +
      `pv ${pv.map(m => m.san).join(' ')}`
    );
  }

  static validatePosition(position) {
    // Check for overlapping pieces
    let allPieces = 0n;
    for (let i = 0; i < 12; i++) {
      if (position.bitboards[i] & allPieces) {
        console.error('Piece overlap detected!');
        return false;
      }
      allPieces |= position.bitboards[i];
    }
    
    // Check king counts
    const whiteKings = position.popCount(position.bitboards[position.WHITE * 6 + 5]);
    const blackKings = position.popCount(position.bitboards[position.BLACK * 6 + 5]);
    
    if (whiteKings !== 1 || blackKings !== 1) {
      console.error(`Invalid king count: ${whiteKings} white, ${blackKings} black`);
      return false;
    }
    
    return true;
  }
}

///////////////////////
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



