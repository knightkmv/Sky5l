## 1. Hauptmodule

### 1.1. `core/`
- `Board.js` - Grundlegende Brettrepräsentation und Bitboard-Operationen
- `Move.js` - Zuggenerierung und -validierung
- `GameState.js` - Spielzustand (Züge, Rochade-Rechte, en passant)
- `Zobrist.js` - Zobrist-Hashing für Positions-Hashing

### 1.2. `search/`
- `Search.js` - Hauptsuchalgorithmus (Alpha-Beta, Iterative Vertiefung)
- `MoveOrdering.js` - Zugreihenfolge-Optimierung
- `Extensions.js` - Suchverlängerungen (Checks, gefährliche Züge)
- `Reductions.js` - Suchreduktionen (LMR, Nullmove)
- `TimeManagement.js` - Zeitmanagement für Turniere

### 1.3. `evaluation/`
- `Material.js` - Materialbewertung
- `PieceSquare.js` - Positionsbewertung
- `PawnStructure.js` - Bauernstruktur
- `Mobility.js` - Figurenmobilität
- `KingSafety.js` - Königsicherheit
- `Threats.js` - Bedrohungsbewertung

### 1.4. `uci/`
- `UCI.js` - UCI-Protokoll-Handler
- `Commands.js` - UCI-Befehlsverarbeitung

### 1.5. `utils/`
- `Helpers.js` - Hilfsfunktionen
- `Bitboard.js` - Bitboard-Operationen
- `Perft.js` - Performance-Testing
///////////////////////////

// ===================== CHESS BOARD IMPLEMENTATION =====================
class Board {
  constructor() {
    // Piece types and colors
    this.PIECE_TYPES = {
      PAWN: 1, KNIGHT: 2, BISHOP: 3, ROOK: 4, QUEEN: 5, KING: 6
    };
    
    this.COLORS = { WHITE: 0, BLACK: 1 };
    
    // Move flags
    this.MOVE_FLAGS = {
      NORMAL: 0, CAPTURE: 1, PROMOTION: 2, 
      ENPASSANT: 3, CASTLING: 4, NULL: 5
    };

    // Bitboards for each piece type and color
    this.bitboards = new Array(12).fill(0n); // [W_PAWN, W_KNIGHT, ..., B_KING]
    
    // Occupancy bitboards
    this.occupancy = new Array(3).fill(0n); // [WHITE, BLACK, BOTH]
    
    // Game state
    this.sideToMove = this.COLORS.WHITE;
    this.castlingRights = 0b1111; // KQkq
    this.enPassantSquare = -1;
    this.halfmoveClock = 0;
    this.fullmoveNumber = 1;
    this.zobristHash = 0n;
    this.gamePhase = 0;
    
    // Move history stack
    this.moveHistory = [];
    
    // Initialize attack tables and zobrist keys
    this.initAttackTables();
    this.initZobrist();
  }

  // ===================== INITIALIZATION =====================
  initAttackTables() {
    // Knight attacks
    this.knightAttacks = new Array(64).fill(0n);
    // King attacks
    this.kingAttacks = new Array(64).fill(0n);
    // Pawn attacks
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

  initZobrist() {
    this.zobristKeys = {
      pieces: Array.from({length: 12}, () => new Array(64)),
      side: 0n,
      castling: new Array(16).fill(0n),
      enPassant: new Array(64).fill(0n)
    };

    // Generate random 64-bit keys
    const rand64 = () => {
      const buf = new BigUint64Array(1);
      crypto.getRandomValues(buf);
      return buf[0];
    };

    for (let i = 0; i < 12; i++) {
      for (let j = 0; j < 64; j++) {
        this.zobristKeys.pieces[i][j] = rand64();
      }
    }
    this.zobristKeys.side = rand64();
    for (let i = 0; i < 16; i++) this.zobristKeys.castling[i] = rand64();
    for (let i = 0; i < 64; i++) this.zobristKeys.enPassant[i] = rand64();
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
    this.sideToMove = parts[1] === 'w' ? this.COLORS.WHITE : this.COLORS.BLACK;
    
    // Parse castling rights
    this.castlingRights = 0;
    if (parts[2] !== '-') {
      for (const c of parts[2]) {
        switch (c) {
          case 'K': this.castlingRights |= 0b0001; break;
          case 'Q': this.castlingRights |= 0b0010; break;
          case 'k': this.castlingRights |= 0b0100; break;
          case 'q': this.castlingRights |= 0b1000; break;
        }
      }
    }
    
    // Parse en passant
    this.enPassantSquare = parts[3] === '-' ? -1 : 
      (parts[3].charCodeAt(0) - 'a'.charCodeAt(0)) + 
      (8 - parseInt(parts[3][1])) * 8;
    
    // Parse halfmove clock and fullmove number
    this.halfmoveClock = parts.length > 4 ? parseInt(parts[4]) : 0;
    this.fullmoveNumber = parts.length > 5 ? parseInt(parts[5]) : 1;
    
    // Update hash
    this.updateZobristHash();
    
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

  updateZobristHash() {
    this.zobristHash = 0n;
    
    // Piece positions
    for (let i = 0; i < 12; i++) {
      let bb = this.bitboards[i];
      while (bb) {
        const sq = this.bitScanForward(bb);
        bb &= bb - 1n;
        this.zobristHash ^= this.zobristKeys.pieces[i][sq];
      }
    }
    
    // Side to move
    if (this.sideToMove === this.COLORS.WHITE) {
      this.zobristHash ^= this.zobristKeys.side;
    }
    
    // Castling rights
    this.zobristHash ^= this.zobristKeys.castling[this.castlingRights];
    
    // En passant
    if (this.enPassantSquare >= 0) {
      this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
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
    fen += this.sideToMove === this.COLORS.WHITE ? ' w ' : ' b ';
    
    // Castling rights
    let castling = '';
    if (this.castlingRights & 0b0001) castling += 'K';
    if (this.castlingRights & 0b0010) castling += 'Q';
    if (this.castlingRights & 0b0100) castling += 'k';
    if (this.castlingRights & 0b1000) castling += 'q';
    fen += castling || '-';
    
    // En passant
    fen += ' ';
    if (this.enPassantSquare >= 0) {
      const file = this.enPassantSquare % 8;
      const rank = Math.floor(this.enPassantSquare / 8);
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

  // ===================== MOVE EXECUTION =====================
  makeMove(move) {
    const undo = {
      zobristHash: this.zobristHash,
      castlingRights: this.castlingRights,
      enPassantSquare: this.enPassantSquare,
      halfmoveClock: this.halfmoveClock,
      capturedPiece: 0
    };
    
    const from = move.from;
    const to = move.to;
    const piece = move.piece;
    const color = this.sideToMove;
    const opponent = color ^ 1;
    
    // Update hash - remove moving piece from source square
    this.zobristHash ^= this.zobristKeys.pieces[color * 6 + piece - 1][from];
    
    // Clear en passant square in hash
    if (this.enPassantSquare >= 0) {
      this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
    }
    
    // Handle captures
    if (move.flags === this.MOVE_FLAGS.CAPTURE || move.flags === this.MOVE_FLAGS.ENPASSANT) {
      let capturedSquare = to;
      let capturedPiece = move.captured;
      
      if (move.flags === this.MOVE_FLAGS.ENPASSANT) {
        capturedSquare = to + (color === this.COLORS.WHITE ? -8 : 8);
        capturedPiece = this.PIECE_TYPES.PAWN;
      }
      
      undo.capturedPiece = capturedPiece;
      
      // Remove captured piece from bitboards
      this.bitboards[opponent * 6 + capturedPiece - 1] ^= 1n << BigInt(capturedSquare);
      this.occupancy[opponent] ^= 1n << BigInt(capturedSquare);
      this.occupancy[2] ^= 1n << BigInt(capturedSquare);
      
      // Update hash - remove captured piece
      this.zobristHash ^= this.zobristKeys.pieces[opponent * 6 + capturedPiece - 1][capturedSquare];
      
      // Reset halfmove clock
      this.halfmoveClock = 0;
    }
    
    // Move the piece
    this.bitboards[color * 6 + piece - 1] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[color] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    this.occupancy[2] ^= (1n << BigInt(from)) | (1n << BigInt(to));
    
    // Update hash - add moving piece to destination square
    this.zobristHash ^= this.zobristKeys.pieces[color * 6 + piece - 1][to];
    
    // Handle promotions
    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
      const promo = move.promotion;
      
      // Remove pawn from destination
      this.bitboards[color * 6 + this.PIECE_TYPES.PAWN - 1] ^= 1n << BigInt(to);
      this.zobristHash ^= this.zobristKeys.pieces[color * 6 + this.PIECE_TYPES.PAWN - 1][to];
      
      // Add promoted piece
      this.bitboards[color * 6 + promo - 1] ^= 1n << BigInt(to);
      this.zobristHash ^= this.zobristKeys.pieces[color * 6 + promo - 1][to];
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
      this.zobristHash ^= this.zobristKeys.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookFrom];
      this.zobristHash ^= this.zobristKeys.pieces[color * 6 + this.PIECE_TYPES.ROOK - 1][rookTo];
    }
    
    // Update castling rights
    const castlingUpdate = this.getCastlingUpdate(from, to, piece, color);
    if (castlingUpdate) {
      this.zobristHash ^= this.zobristKeys.castling[this.castlingRights];
      this.castlingRights &= ~castlingUpdate;
      this.zobristHash ^= this.zobristKeys.castling[this.castlingRights];
      undo.castlingRights = this.castlingRights | castlingUpdate; // Store original value
    }
    
    // Set en passant square
    this.enPassantSquare = -1;
    if (piece === this.PIECE_TYPES.PAWN && Math.abs(to - from) === 16) {
      this.enPassantSquare = from + (color === this.COLORS.WHITE ? 8 : -8);
      this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
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
    this.sideToMove = opponent;
    this.zobristHash ^= this.zobristKeys.side;
    
    // Push to history
    this.moveHistory.push({
      move,
      zobristHash: this.zobristHash,
      castlingRights: this.castlingRights,
      enPassantSquare: this.enPassantSquare,
      halfmoveClock: this.halfmoveClock,
      fullmoveNumber: this.fullmoveNumber,
      capturedPiece: undo.capturedPiece
    });
    
    return undo;
  }

  undoMove(move, undo) {
    const from = move.from;
    const to = move.to;
    const piece = move.piece;
    const color = this.sideToMove ^ 1; // Opposite of current side
    const opponent = color ^ 1;
    
    // Switch side first
    this.sideToMove = color;
    this.zobristHash ^= this.zobristKeys.side;
    
    // Restore fullmove number
    if (color === this.COLORS.BLACK) {
      this.fullmoveNumber--;
    }
    
    // Restore castling rights
    if (this.castlingRights !== undo.castlingRights) {
      this.zobristHash ^= this.zobristKeys.castling[this.castlingRights];
      this.castlingRights = undo.castlingRights;
      this.zobristHash ^= this.zobristKeys.castling[this.castlingRights];
    }
    
    // Restore en passant
    if (this.enPassantSquare !== undo.enPassantSquare) {
      if (this.enPassantSquare >= 0) this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
      this.enPassantSquare = undo.enPassantSquare;
      if (this.enPassantSquare >= 0) this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
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
      this.bitboards[color * 6 + this.PIECE_TYPES.PAWN - 1] ^= 1n << BigInt(to);
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
      this.bitboards[opponent * 6 + undo.capturedPiece - 1] ^= 1n << BigInt(capturedSquare);
      this.occupancy[opponent] ^= 1n << BigInt(capturedSquare);
      this.occupancy[2] ^= 1n << BigInt(capturedSquare);
    }
    
    // Pop from history
    this.moveHistory.pop();
  }

  makeNullMove() {
    const undo = {
      zobristHash: this.zobristHash,
      enPassantSquare: this.enPassantSquare
    };
    
    // Clear en passant square in hash
    if (this.enPassantSquare >= 0) {
      this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
      this.enPassantSquare = -1;
    }
    
    // Switch side
    this.sideToMove ^= 1;
    this.zobristHash ^= this.zobristKeys.side;
    
    return undo;
  }

  undoNullMove(undo) {
    // Restore en passant
    if (this.enPassantSquare !== undo.enPassantSquare) {
      if (this.enPassantSquare >= 0) this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
      this.enPassantSquare = undo.enPassantSquare;
      if (this.enPassantSquare >= 0) this.zobristHash ^= this.zobristKeys.enPassant[this.enPassantSquare];
    }
    
    // Switch side back
    this.sideToMove ^= 1;
    this.zobristHash ^= this.zobristKeys.side;
  }

  // ===================== UTILITY FUNCTIONS =====================
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

  getCastlingUpdate(from, to, piece, color) {
    let update = 0;
    
    // King move removes both castling rights
    if (piece === this.PIECE_TYPES.KING) {
      update = color === this.COLORS.WHITE ? 0b0011 : 0b1100;
    } 
    // Rook move removes corresponding castling right
    else if (piece === this.PIECE_TYPES.ROOK) {
      if (color === this.COLORS.WHITE) {
        if (from === 0) update |= 0b0010; // Queenside
        if (from === 7) update |= 0b0001; // Kingside
      } else {
        if (from === 56) update |= 0b1000; // Queenside
        if (from === 63) update |= 0b0100; // Kingside
      }
    }
    
    // Rook capture removes corresponding castling right
    if (this.bitboards[(color ^ 1) * 6 + this.PIECE_TYPES.ROOK - 1] & (1n << BigInt(to))) {
      if (to === 0) update |= 0b0010; // White queenside
      if (to === 7) update |= 0b0001; // White kingside
      if (to === 56) update |= 0b1000; // Black queenside
      if (to === 63) update |= 0b0100; // Black kingside
    }
    
    return update;
  }

  // ===================== GAME STATE CHECKS =====================
  isInCheck() {
    const kingSquare = this.bitScanForward(
      this.bitboards[this.sideToMove * 6 + this.PIECE_TYPES.KING - 1]
    );
    return this.isSquareAttacked(kingSquare, this.sideToMove ^ 1);
  }

  isSquareAttacked(square, byColor) {
    // Pawns
    if (this.pawnAttacks[byColor ^ 1][square] & 
        this.bitboards[byColor * 6 + this.PIECE_TYPES.PAWN - 1]) {
      return true;
    }
    
    // Knights
    if (this.knightAttacks[square] & 
        this.bitboards[byColor * 6 + this.PIECE_TYPES.KNIGHT - 1]) {
      return true;
    }
    
    // King
    if (this.kingAttacks[square] & 
        this.bitboards[byColor * 6 + this.PIECE_TYPES.KING - 1]) {
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

  getSliderAttacks(pieceType, square) {
    const occupancy = this.occupancy[2];
    
    if (pieceType === this.PIECE_TYPES.BISHOP) {
      return this.getBishopAttacks(square, occupancy);
    } else if (pieceType === this.PIECE_TYPES.ROOK) {
      return this.getRookAttacks(square, occupancy);
    } else if (pieceType === this.PIECE_TYPES.QUEEN) {
      return this.getBishopAttacks(square, occupancy) | 
             this.getRookAttacks(square, occupancy);
    }
    
    return 0n;
  }

  getBishopAttacks(square, occupancy) {
    // Simplified bishop attack calculation
    let attacks = 0n;
    const [rank, file] = [Math.floor(square / 8), square % 8];
    
    // Diagonal \
    for (let r = rank + 1, f = file + 1; r < 8 && f < 8; r++, f++) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1, f = file - 1; r >= 0 && f >= 0; r--, f--) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    // Diagonal /
    for (let r = rank + 1, f = file - 1; r < 8 && f >= 0; r++, f--) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1, f = file + 1; r >= 0 && f < 8; r--, f++) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    return attacks;
  }

  getRookAttacks(square, occupancy) {
    // Simplified rook attack calculation
    let attacks = 0n;
    const [rank, file] = [Math.floor(square / 8), square % 8];
    
    // Horizontal
    for (let f = file + 1; f < 8; f++) {
      const s = rank * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let f = file - 1; f >= 0; f--) {
      const s = rank * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    // Vertical
    for (let r = rank + 1; r < 8; r++) {
      const s = r * 8 + file;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1; r >= 0; r--) {
      const s = r * 8 + file;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    return attacks;
  }

  isDrawn() {
    // 50-move rule
    if (this.halfmoveClock >= 100) {
      return true;
    }
    
    // Insufficient material
    if (this.isInsufficientMaterial()) {
      return true;
    }
    
    // Threefold repetition
    if (this.isThreefoldRepetition()) {
      return true;
    }
    
    return false;
  }

  isInsufficientMaterial() {
    const whitePieces = this.popCount(this.occupancy[this.COLORS.WHITE]);
    const blackPieces = this.popCount(this.occupancy[this.COLORS.BLACK]);
    
    // King vs King
    if (whitePieces === 1 && blackPieces === 1) {
      return true;
    }
    
    // King + minor piece vs King
    if ((whitePieces === 2 && blackPieces === 1) || 
        (whitePieces === 1 && blackPieces === 2)) {
      const minorPieces = this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.KNIGHT - 1] |
                         this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.BISHOP - 1] |
                         this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.KNIGHT - 1] |
                         this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.BISHOP - 1];
      
      if (this.popCount(minorPieces) === 1) {
        return true;
      }
    }
    
    // King + bishop vs King + bishop with bishops on same color
    if (whitePieces === 2 && blackPieces === 2) {
      const whiteBishops = this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.BISHOP - 1];
      const blackBishops = this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.BISHOP - 1];
      
      if (whiteBishops && blackBishops) {
        const whiteBishopSquare = this.bitScanForward(whiteBishops);
        const blackBishopSquare = this.bitScanForward(blackBishops);
        
        // Bishops on same color
        if ((whiteBishopSquare + blackBishopSquare) % 2 === 0) {
          return true;
        }
      }
    }
    
    return false;
  }

  isThreefoldRepetition() {
    if (this.moveHistory.length < 8) return false;
    
    let repetitions = 0;
    const currentHash = this.zobristHash;
    
    // Check last 8 positions (including current)
    for (let i = this.moveHistory.length - 1; i >= 0 && i >= this.moveHistory.length - 8; i--) {
      if (this.moveHistory[i].zobristHash === currentHash) {
        repetitions++;
        if (repetitions >= 3) return true;
      }
    }
    
    return false;
  }

  gamePhase() {
    // Calculate game phase based on remaining material
    let phase = 0;
    
    // Count non-pawn, non-king pieces
    for (let color = 0; color < 2; color++) {
      for (let piece = this.PIECE_TYPES.KNIGHT; piece <= this.PIECE_TYPES.QUEEN; piece++) {
        const count = this.popCount(this.bitboards[color * 6 + piece - 1]);
        
        switch (piece) {
          case this.PIECE_TYPES.KNIGHT:
          case this.PIECE_TYPES.BISHOP:
            phase += count * 1;
            break;
          case this.PIECE_TYPES.ROOK:
            phase += count * 2;
            break;
          case this.PIECE_TYPES.QUEEN:
            phase += count * 4;
            break;
        }
      }
    }
    
    // Cap phase at 24 (opening) to 0 (endgame)
    return Math.min(24, Math.max(0, phase));
  }
}

export default Board;

/////////////////////////////
// ===================== MOVE GENERATION IMPLEMENTATION =====================
class MoveGenerator {
  constructor(board) {
    this.board = board;
    
    // Initialize attack tables if not already in Board
    this.initAttackTables();
  }

  // ===================== INITIALIZATION =====================
  initAttackTables() {
    // Knight attacks
    this.knightAttacks = new Array(64).fill(0n);
    // King attacks
    this.kingAttacks = new Array(64).fill(0n);
    // Pawn attacks
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
        if (square % 8 > 0) this.pawnAttacks[this.board.COLORS.WHITE][square] |= 1n << BigInt(square - 9);
        if (square % 8 < 7) this.pawnAttacks[this.board.COLORS.WHITE][square] |= 1n << BigInt(square - 7);
      }
      if (square < 56) { // Black pawns
        if (square % 8 > 0) this.pawnAttacks[this.board.COLORS.BLACK][square] |= 1n << BigInt(square + 7);
        if (square % 8 < 7) this.pawnAttacks[this.board.COLORS.BLACK][square] |= 1n << BigInt(square + 9);
      }
    }
  }

  // ===================== MOVE GENERATION =====================
  generateMoves(includeQuiets = true) {
    const moves = [];
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const kingSquare = this.board.bitScanForward(
      this.board.bitboards[us * 6 + this.board.PIECE_TYPES.KING - 1]
    );
    
    // Detect pins and checks
    const { pinnedPieces, checkers } = this.detectPinsAndChecks(kingSquare, us);
    const inCheck = checkers !== 0n;
    const doubleCheck = this.board.popCount(checkers) > 1;
    
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

  detectPinsAndChecks(kingSquare, color) {
    const them = color ^ 1;
    let pinnedPieces = 0n;
    let checkers = 0n;
    
    // Check for sliding piece checks/pins
    const sliders = this.board.bitboards[them * 6 + this.board.PIECE_TYPES.QUEEN - 1] |
                   this.board.bitboards[them * 6 + this.board.PIECE_TYPES.ROOK - 1] |
                   this.board.bitboards[them * 6 + this.board.PIECE_TYPES.BISHOP - 1];
    
    let sliderBB = sliders;
    while (sliderBB) {
      const sq = this.board.bitScanForward(sliderBB);
      sliderBB &= sliderBB - 1n;
      
      const pieceType = this.getPieceAt(sq, them);
      const attacks = this.getSliderAttacks(pieceType, sq);
      
      // If the slider attacks the king, it's a checker
      if (attacks & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    // Check for knight checks
    let knights = this.board.bitboards[them * 6 + this.board.PIECE_TYPES.KNIGHT - 1];
    while (knights) {
      const sq = this.board.bitScanForward(knights);
      knights &= knights - 1n;
      
      if (this.knightAttacks[sq] & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    // Check for pawn checks
    let pawns = this.board.bitboards[them * 6 + this.board.PIECE_TYPES.PAWN - 1];
    while (pawns) {
      const sq = this.board.bitScanForward(pawns);
      pawns &= pawns - 1n;
      
      if (this.pawnAttacks[them][sq] & (1n << BigInt(kingSquare))) {
        checkers |= 1n << BigInt(sq);
      }
    }
    
    return { pinnedPieces, checkers };
  }

  generateEvasions(moves, kingSquare, checkers, pinnedPieces, doubleCheck) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    
    // King moves - must move out of attack
    this.generateKingMoves(moves, kingSquare, true);
    
    // If double check, only king moves are legal
    if (doubleCheck) return;
    
    // Block or capture the checking piece
    const checkerSquare = this.board.bitScanForward(checkers);
    const checkerPiece = this.getPieceAt(checkerSquare, them);
    const checkerMask = this.getEvasionMask(kingSquare, checkerSquare, checkerPiece);
    
    // Generate blocking moves or captures of checking piece
    this.generateBlockingMoves(moves, checkerMask, pinnedPieces);
  }

  generateQuietMoves(moves, kingSquare, pinnedPieces) {
    const us = this.board.sideToMove;
    
    // Pawn pushes
    this.generatePawnPushes(moves, kingSquare, pinnedPieces);
    
    // Knight moves
    this.generatePieceMoves(
      moves, 
      this.board.PIECE_TYPES.KNIGHT, 
      this.knightAttacks, 
      kingSquare, 
      pinnedPieces,
      false
    );
    
    // Bishop moves
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.BISHOP,
      kingSquare,
      pinnedPieces,
      false
    );
    
    // Rook moves
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.ROOK,
      kingSquare,
      pinnedPieces,
      false
    );
    
    // Queen moves
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.QUEEN,
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
    const us = this.board.sideToMove;
    const them = us ^ 1;
    
    // Pawn captures
    this.generatePawnCaptures(moves, kingSquare, pinnedPieces);
    
    // Knight captures
    this.generatePieceMoves(
      moves, 
      this.board.PIECE_TYPES.KNIGHT, 
      this.knightAttacks, 
      kingSquare, 
      pinnedPieces,
      true
    );
    
    // Bishop captures
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.BISHOP,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // Rook captures
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.ROOK,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // Queen captures
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.QUEEN,
      kingSquare,
      pinnedPieces,
      true
    );
    
    // King captures
    this.generateKingMoves(moves, kingSquare, true);
  }

  generateSpecialMoves(moves, kingSquare, pinnedPieces) {
    // En passant
    if (this.board.enPassantSquare >= 0) {
      this.generateEnPassant(moves, kingSquare, pinnedPieces);
    }
  }

  // ===================== PIECE-SPECIFIC MOVE GENERATION =====================
  generatePawnPushes(moves, kingSquare, pinnedPieces) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const pawns = this.board.bitboards[us * 6 + this.board.PIECE_TYPES.PAWN - 1];
    const empty = ~this.board.occupancy[2];
    const promotionRank = us === this.board.COLORS.WHITE ? 7 : 0;
    
    let pawnBB = pawns;
    while (pawnBB) {
      const from = this.board.bitScanForward(pawnBB);
      pawnBB &= pawnBB - 1n;
      
      // Check if pawn is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      if (isPinned) continue;
      
      const push1 = from + (us === this.board.COLORS.WHITE ? 8 : -8);
      if (empty & (1n << BigInt(push1))) {
        // Single push
        if (Math.floor(push1 / 8) === promotionRank) {
          this.addPromotions(moves, from, push1, this.board.PIECE_TYPES.PAWN, 0);
        } else {
          this.addMove(moves, from, push1, this.board.PIECE_TYPES.PAWN, 0);
          
          // Double push
          const rank = Math.floor(from / 8);
          const push2 = from + (us === this.board.COLORS.WHITE ? 16 : -16);
          if ((us === this.board.COLORS.WHITE && rank === 1) || 
              (us === this.board.COLORS.BLACK && rank === 6)) {
            if (empty & (1n << BigInt(push2))) {
              this.addMove(moves, from, push2, this.board.PIECE_TYPES.PAWN, 0);
            }
          }
        }
      }
    }
  }

  generatePawnCaptures(moves, kingSquare, pinnedPieces) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const pawns = this.board.bitboards[us * 6 + this.board.PIECE_TYPES.PAWN - 1];
    const enemyPieces = this.board.occupancy[them];
    const promotionRank = us === this.board.COLORS.WHITE ? 7 : 0;
    
    let pawnBB = pawns;
    while (pawnBB) {
      const from = this.board.bitScanForward(pawnBB);
      pawnBB &= pawnBB - 1n;
      
      // Check if pawn is pinned
      const isPinned = pinnedPieces & (1n << BigInt(from));
      
      // Generate captures
      const attacks = this.pawnAttacks[us][from] & enemyPieces;
      let attackBB = attacks;
      while (attackBB) {
        const to = this.board.bitScanForward(attackBB);
        attackBB &= attackBB - 1n;
        
        // Check if capture is legal for pinned pawn
        if (isPinned && !this.isMoveAlongPinRay(from, to, kingSquare)) {
          continue;
        }
        
        const captured = this.getPieceAt(to, them);
        if (Math.floor(to / 8) === promotionRank) {
          this.addPromotions(moves, from, to, this.board.PIECE_TYPES.PAWN, captured);
        } else {
          this.addMove(moves, from, to, this.board.PIECE_TYPES.PAWN, captured);
        }
      }
    }
  }

  generateEnPassant(moves, kingSquare, pinnedPieces) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const epSquare = this.board.enPassantSquare;
    const pawns = this.board.bitboards[us * 6 + this.board.PIECE_TYPES.PAWN - 1];
    
    // Get pawns that can capture en passant
    const attackers = pawns & this.pawnAttacks[them][epSquare];
    let attackerBB = attackers;
    
    while (attackerBB) {
      const from = this.board.bitScanForward(attackerBB);
      attackerBB &= attackerBB - 1n;
      
      // Check if pawn is pinned
      if (pinnedPieces & (1n << BigInt(from))) {
        // Special check for en passant pins
        if (!this.isEnPassantLegal(from, epSquare, kingSquare, us)) {
          continue;
        }
      }
      
      this.addMove(moves, from, epSquare, this.board.PIECE_TYPES.PAWN, 
                  this.board.PIECE_TYPES.PAWN, this.board.MOVE_FLAGS.ENPASSANT);
    }
  }

  generatePieceMoves(moves, pieceType, moveTable, kingSquare, pinnedPieces, capturesOnly) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const pieces = this.board.bitboards[us * 6 + pieceType - 1];
    const targets = capturesOnly ? this.board.occupancy[them] : ~this.board.occupancy[us];
    
    let pieceBB = pieces;
    while (pieceBB) {
      const from = this.board.bitScanForward(pieceBB);
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
        const to = this.board.bitScanForward(movesBB);
        movesBB &= movesBB - 1n;
        
        const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
        this.addMove(moves, from, to, pieceType, captured);
      }
    }
  }

  generateSliderMoves(moves, pieceType, kingSquare, pinnedPieces, capturesOnly) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const pieces = this.board.bitboards[us * 6 + pieceType - 1];
    const targets = capturesOnly ? this.board.occupancy[them] : ~this.board.occupancy[us];
    
    let pieceBB = pieces;
    while (pieceBB) {
      const from = this.board.bitScanForward(pieceBB);
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
        const to = this.board.bitScanForward(attacks);
        attacks &= attacks - 1n;
        
        const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
        this.addMove(moves, from, to, pieceType, captured);
      }
    }
  }

  generateKingMoves(moves, fromSquare, capturesOnly) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    const targets = capturesOnly ? this.board.occupancy[them] : ~this.board.occupancy[us];
    
    // Normal king moves
    let movesBB = this.kingAttacks[fromSquare] & targets;
    while (movesBB) {
      const to = this.board.bitScanForward(movesBB);
      movesBB &= movesBB - 1n;
      
      // Make sure destination is not attacked
      if (this.isSquareAttacked(to, them)) continue;
      
      const captured = capturesOnly ? this.getPieceAt(to, them) : 0;
      this.addMove(moves, fromSquare, to, this.board.PIECE_TYPES.KING, captured);
    }
  }

  generateCastling(moves, kingSquare) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    
    if (this.board.isInCheck()) return;
    
    const castlingRights = this.board.castlingRights;
    if (!castlingRights) return;
    
    // Generate kingside castling
    if (castlingRights & (us === this.board.COLORS.WHITE ? 0b0001 : 0b0100)) {
      this.generateCastle(moves, kingSquare, true, us, them);
    }
    
    // Generate queenside castling
    if (castlingRights & (us === this.board.COLORS.WHITE ? 0b0010 : 0b1000)) {
      this.generateCastle(moves, kingSquare, false, us, them);
    }
  }

  generateCastle(moves, kingSquare, kingside, us, them) {
    const [rookFrom, rookTo, kingTo, emptySquares, safeSquares] = 
      this.getCastleSquares(kingSquare, kingside, us);
    
    // Check if squares are empty and not attacked
    if ((this.board.occupancy[2] & emptySquares) !== 0n) return;
    if (this.areSquaresAttacked(safeSquares, them)) return;
    
    this.addMove(
      moves, 
      kingSquare, 
      kingTo, 
      this.board.PIECE_TYPES.KING, 
      0, 
      this.board.MOVE_FLAGS.CASTLING,
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
      this.board.PIECE_TYPES.QUEEN,
      this.board.PIECE_TYPES.ROOK,
      this.board.PIECE_TYPES.BISHOP,
      this.board.PIECE_TYPES.KNIGHT
    ]) {
      this.addMove(
        moves, 
        from, 
        to, 
        piece, 
        captured, 
        this.board.MOVE_FLAGS.PROMOTION,
        promo
      );
    }
  }

  getPieceAt(square, color) {
    for (let type = 1; type <= 6; type++) {
      if (this.board.bitboards[color * 6 + type - 1] & (1n << BigInt(square))) {
        return type;
      }
    }
    return 0;
  }

  getSliderAttacks(pieceType, square) {
    const occupancy = this.board.occupancy[2];
    
    if (pieceType === this.board.PIECE_TYPES.BISHOP) {
      return this.getBishopAttacks(square, occupancy);
    } else if (pieceType === this.board.PIECE_TYPES.ROOK) {
      return this.getRookAttacks(square, occupancy);
    } else if (pieceType === this.board.PIECE_TYPES.QUEEN) {
      return this.getBishopAttacks(square, occupancy) | 
             this.getRookAttacks(square, occupancy);
    }
    
    return 0n;
  }

  getBishopAttacks(square, occupancy) {
    let attacks = 0n;
    const [rank, file] = [Math.floor(square / 8), square % 8];
    
    // Diagonal \
    for (let r = rank + 1, f = file + 1; r < 8 && f < 8; r++, f++) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1, f = file - 1; r >= 0 && f >= 0; r--, f--) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    // Diagonal /
    for (let r = rank + 1, f = file - 1; r < 8 && f >= 0; r++, f--) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1, f = file + 1; r >= 0 && f < 8; r--, f++) {
      const s = r * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    return attacks;
  }

  getRookAttacks(square, occupancy) {
    let attacks = 0n;
    const [rank, file] = [Math.floor(square / 8), square % 8];
    
    // Horizontal
    for (let f = file + 1; f < 8; f++) {
      const s = rank * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let f = file - 1; f >= 0; f--) {
      const s = rank * 8 + f;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    // Vertical
    for (let r = rank + 1; r < 8; r++) {
      const s = r * 8 + file;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    for (let r = rank - 1; r >= 0; r--) {
      const s = r * 8 + file;
      attacks |= 1n << BigInt(s);
      if (occupancy & (1n << BigInt(s))) break;
    }
    
    return attacks;
  }

  isSquareAttacked(square, byColor) {
    // Pawns
    if (this.pawnAttacks[byColor ^ 1][square] & 
        this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.PAWN - 1]) {
      return true;
    }
    
    // Knights
    if (this.knightAttacks[square] & 
        this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.KNIGHT - 1]) {
      return true;
    }
    
    // King
    if (this.kingAttacks[square] & 
        this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.KING - 1]) {
      return true;
    }
    
    // Sliding pieces
    const queens = this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.QUEEN - 1];
    const rooks = queens | this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.ROOK - 1];
    const bishops = queens | this.board.bitboards[byColor * 6 + this.board.PIECE_TYPES.BISHOP - 1];
    
    // Rooks/Queens
    if (this.getSliderAttacks(this.board.PIECE_TYPES.ROOK, square) & rooks) {
      return true;
    }
    
    // Bishops/Queens
    if (this.getSliderAttacks(this.board.PIECE_TYPES.BISHOP, square) & bishops) {
      return true;
    }
    
    return false;
  }

  areSquaresAttacked(squares, byColor) {
    let bb = squares;
    while (bb) {
      const sq = this.board.bitScanForward(bb);
      bb &= bb - 1n;
      
      if (this.isSquareAttacked(sq, byColor)) {
        return true;
      }
    }
    return false;
  }

  getEvasionMask(kingSquare, checkerSquare, checkerPiece) {
    if (checkerPiece === this.board.PIECE_TYPES.KNIGHT || 
        checkerPiece === this.board.PIECE_TYPES.PAWN) {
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
    const capturedPawnSquare = epSquare + (color === this.board.COLORS.WHITE ? -8 : 8);
    const newOccupancy = this.board.occupancy[2] ^ 
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
          if (piece === this.board.PIECE_TYPES.ROOK || piece === this.board.PIECE_TYPES.QUEEN) {
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
    if (color === this.board.COLORS.WHITE) {
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

  generateBlockingMoves(moves, checkerMask, pinnedPieces) {
    const us = this.board.sideToMove;
    const them = us ^ 1;
    
    // Generate moves that block or capture the checking piece
    this.generatePieceMoves(
      moves, 
      this.board.PIECE_TYPES.KNIGHT, 
      this.knightAttacks, 
      this.board.bitScanForward(
        this.board.bitboards[us * 6 + this.board.PIECE_TYPES.KING - 1]
      ), 
      pinnedPieces,
      true
    );
    
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.BISHOP,
      this.board.bitScanForward(
        this.board.bitboards[us * 6 + this.board.PIECE_TYPES.KING - 1]
      ),
      pinnedPieces,
      true
    );
    
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.ROOK,
      this.board.bitScanForward(
        this.board.bitboards[us * 6 + this.board.PIECE_TYPES.KING - 1]
      ),
      pinnedPieces,
      true
    );
    
    this.generateSliderMoves(
      moves,
      this.board.PIECE_TYPES.QUEEN,
      this.board.bitScanForward(
        this.board.bitboards[us * 6 + this.board.PIECE_TYPES.KING - 1]
      ),
      pinnedPieces,
      true
    );
    
    // Filter moves to only those that block or capture the checking piece
    for (let i = moves.length - 1; i >= 0; i--) {
      const move = moves[i];
      if (!(checkerMask & (1n << BigInt(move.to))) && 
          move.captured !== this.board.PIECE_TYPES.KING) {
        moves.splice(i, 1);
      }
    }
  }
}

export default MoveGenerator;

/////////////////////////////
// ===================== GAME STATE MODULE =====================
// Handles all game state management including move execution, 
// position tracking, and game termination checks

class GameState {
  constructor() {
    // Constants
    this.PIECE_TYPES = {
      PAWN: 1, KNIGHT: 2, BISHOP: 3, ROOK: 4, QUEEN: 5, KING: 6
    };
    
    this.COLORS = { WHITE: 0, BLACK: 1 };
    
    this.MOVE_FLAGS = {
      NORMAL: 0, 
      CAPTURE: 1, 
      PROMOTION: 2, 
      ENPASSANT: 3, 
      CASTLING: 4, 
      NULL: 5
    };
    
    // Current game state
    this.bitboards = new BigUint64Array(12); // 2 colors * 6 pieces
    this.occupancy = new BigUint64Array(3);  // [white, black, combined]
    this.side = this.COLORS.WHITE;
    this.castling = 0b1111; // KQkq
    this.epSquare = -1;
    this.halfmoveClock = 0;
    this.fullmoveNumber = 1;
    this.hash = 0n;
    this.ply = 0;
    this.stack = []; // Move history stack
    
    // Initialize Zobrist hashing
    this.initZobrist();
  }

  // ===================== INITIALIZATION =====================
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

  // ===================== MOVE EXECUTION =====================
  makeMove(move) {
    const undo = {
      hash: this.hash,
      castling: this.castling,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock,
      fullmoveNumber: this.fullmoveNumber,
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

  makeNullMove() {
    const undo = {
      hash: this.hash,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock
    };
    
    // Clear ep square in hash
    if (this.epSquare >= 0) {
      this.hash ^= this.zobrist.ep[this.epSquare];
      this.epSquare = -1;
    }
    
    // Increment halfmove clock (unless in check)
    if (!this.isInCheck()) {
      this.halfmoveClock++;
    }
    
    // Switch side
    this.side ^= 1;
    this.hash ^= this.zobrist.side;
    
    // Push to stack
    this.stack.push({
      move: null,
      hash: this.hash,
      castling: this.castling,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock,
      fullmoveNumber: this.fullmoveNumber,
      captured: 0
    });
    
    return undo;
  }

  undoNullMove(undo) {
    // Pop the stack
    this.stack.pop();
    this.ply--;
    
    // Restore state
    this.side ^= 1;
    this.hash = undo.hash;
    this.epSquare = undo.epSquare;
    this.halfmoveClock = undo.halfmoveClock;
  }

  // ===================== GAME STATE CHECKS =====================
  isInCheck(color = this.side) {
    const kingSquare = this.bitScanForward(
      this.bitboards[color * 6 + this.PIECE_TYPES.KING - 1]
    );
    return this.isSquareAttacked(kingSquare, color ^ 1);
  }

  isDrawn() {
    // 50-move rule
    if (this.halfmoveClock >= 100) {
      return true;
    }
    
    // Insufficient material
    if (this.hasInsufficientMaterial()) {
      return true;
    }
    
    // Threefold repetition
    if (this.hasThreefoldRepetition()) {
      return true;
    }
    
    // Stalemate
    if (!this.isInCheck() && this.generateMoves().length === 0) {
      return true;
    }
    
    return false;
  }

  hasInsufficientMaterial() {
    const whitePieces = this.occupancy[this.COLORS.WHITE];
    const blackPieces = this.occupancy[this.COLORS.BLACK];
    const allPieces = this.occupancy[2];
    
    // King vs King
    if (allPieces === (whitePieces | blackPieces)) {
      return true;
    }
    
    // King + minor vs King
    const whiteMinors = this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.KNIGHT - 1] | 
                       this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.BISHOP - 1];
    const blackMinors = this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.KNIGHT - 1] | 
                       this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.BISHOP - 1];
    
    if (this.popCount(whitePieces) === 1 && this.popCount(blackPieces) <= 2 && 
        this.popCount(blackMinors) <= 1) {
      return true;
    }
    
    if (this.popCount(blackPieces) === 1 && this.popCount(whitePieces) <= 2 && 
        this.popCount(whiteMinors) <= 1) {
      return true;
    }
    
    // King + Bishop vs King + Bishop with bishops on same color
    if (this.popCount(whitePieces) === 2 && this.popCount(blackPieces) === 2) {
      const whiteBishops = this.bitboards[this.COLORS.WHITE * 6 + this.PIECE_TYPES.BISHOP - 1];
      const blackBishops = this.bitboards[this.COLORS.BLACK * 6 + this.PIECE_TYPES.BISHOP - 1];
      
      if (whiteBishops && blackBishops) {
        const whiteBishopSquare = this.bitScanForward(whiteBishops);
        const blackBishopSquare = this.bitScanForward(blackBishops);
        
        // Check if bishops are on same color
        if (((whiteBishopSquare + blackBishopSquare) % 2) === 0) {
          return true;
        }
      }
    }
    
    return false;
  }

  hasThreefoldRepetition() {
    if (this.stack.length < 8) return false;
    
    let repetitions = 0;
    const currentHash = this.hash;
    
    // Check last 8 positions (including current)
    for (let i = this.stack.length - 1; i >= Math.max(0, this.stack.length - 8); i--) {
      if (this.stack[i].hash === currentHash) {
        repetitions++;
        if (repetitions >= 3) return true;
      }
    }
    
    return false;
  }

  // ===================== HELPER METHODS =====================
  getCastlingUpdate(from, to, piece, color) {
    let update = 0;
    const kingSide = color === this.COLORS.WHITE ? 0b0001 : 0b0100;
    const queenSide = color === this.COLORS.WHITE ? 0b0010 : 0b1000;
    
    // King moved
    if (piece === this.PIECE_TYPES.KING) {
      update |= kingSide | queenSide;
    }
    // Rook moved
    else if (piece === this.PIECE_TYPES.ROOK) {
      if (from === (color === this.COLORS.WHITE ? 0 : 56)) update |= queenSide;
      if (from === (color === this.COLORS.WHITE ? 7 : 63)) update |= kingSide;
    }
    // Rook captured
    else if (this.castling) {
      if (to === (color === this.COLORS.WHITE ? 0 : 56)) update |= queenSide;
      if (to === (color === this.COLORS.WHITE ? 7 : 63)) update |= kingSide;
    }
    
    return update;
  }

  bitScanForward(bb) {
    if (bb === 0n) return -1;
    return 63 - Math.clz32(Number(bb & 0xFFFFFFFFn)) + 
           (bb > 0xFFFFFFFFn ? 32 : 0);
  }

  popCount(bb) {
    let count = 0;
    while (bb) {
      count++;
      bb &= bb - 1n;
    }
    return count;
  }

  getDynamicContempt() {
    // Return contempt factor based on engine strength and position
    return 0; // Default implementation
  }

  gamePhase() {
    // Calculate game phase (0 = opening, 256 = endgame)
    let phase = 256;
    
    // Subtract for each piece remaining
    for (let piece = this.PIECE_TYPES.PAWN; piece <= this.PIECE_TYPES.QUEEN; piece++) {
      phase -= this.popCount(this.bitboards[this.COLORS.WHITE * 6 + piece - 1] | 
               this.bitboards[this.COLORS.BLACK * 6 + piece - 1]) * 
               [0, 0, 1, 1, 2, 4][piece]; // Piece weights
    }
    
    return Math.max(0, phase);
  }
}

export default GameState;
//////////////////////////////
// ===================== ZOBRIST HASHING MODULE =====================
// Handles all Zobrist hashing functionality for position identification,
// repetition detection, and transposition table lookups

class Zobrist {
  constructor() {
    // Constants
    this.PIECE_TYPES = {
      PAWN: 1, KNIGHT: 2, BISHOP: 3, ROOK: 4, QUEEN: 5, KING: 6
    };
    
    this.COLORS = { WHITE: 0, BLACK: 1 };
    
    // Initialize all Zobrist keys
    this.keys = {
      pieces: this.initPieceKeys(),
      side: this.random64(),
      castling: this.initCastlingKeys(),
      ep: this.initEnPassantKeys()
    };
  }

  // ===================== INITIALIZATION =====================
  initPieceKeys() {
    // [color][piece][square]
    const pieces = Array.from({length: 2}, () => 
      Array.from({length: 6}, () => 
        new Array(64).fill(0n)
      )
    );
    
    for (let color = 0; color < 2; color++) {
      for (let piece = 0; piece < 6; piece++) {
        for (let square = 0; square < 64; square++) {
          pieces[color][piece][square] = this.random64();
        }
      }
    }
    
    return pieces;
  }

  initCastlingKeys() {
    // 16 possible castling right combinations (4 bits)
    const keys = new Array(16).fill(0n);
    for (let i = 0; i < 16; i++) {
      keys[i] = this.random64();
    }
    return keys;
  }

  initEnPassantKeys() {
    // One key for each possible en passant file (8 files)
    const keys = new Array(8).fill(0n);
    for (let i = 0; i < 8; i++) {
      keys[i] = this.random64();
    }
    return keys;
  }

  random64() {
    // Generate cryptographically secure random 64-bit number
    const buf = new BigUint64Array(1);
    crypto.getRandomValues(buf);
    return buf[0];
  }

  // ===================== HASH OPERATIONS =====================
  computeInitialHash(position) {
    let hash = 0n;
    
    // Hash piece positions
    for (let color = 0; color < 2; color++) {
      for (let piece = 0; piece < 6; piece++) {
        let bb = position.bitboards[color * 6 + piece];
        while (bb) {
          const sq = position.bitScanForward(bb);
          bb &= bb - 1n;
          hash ^= this.keys.pieces[color][piece][sq];
        }
      }
    }
    
    // Hash side to move
    if (position.side === this.COLORS.WHITE) {
      hash ^= this.keys.side;
    }
    
    // Hash castling rights
    hash ^= this.keys.castling[position.castling];
    
    // Hash en passant
    if (position.epSquare >= 0) {
      hash ^= this.getEnPassantKey(position.epSquare);
    }
    
    return hash;
  }

  updatePieceHash(hash, color, piece, square) {
    return hash ^ this.keys.pieces[color][piece][square];
  }

  updateSideHash(hash) {
    return hash ^ this.keys.side;
  }

  updateCastlingHash(hash, castlingRights) {
    return hash ^ this.keys.castling[castlingRights];
  }

  updateEnPassantHash(hash, epSquare) {
    if (epSquare >= 0) {
      return hash ^ this.getEnPassantKey(epSquare);
    }
    return hash;
  }

  getEnPassantKey(epSquare) {
    const file = epSquare % 8;
    return this.keys.ep[file];
  }

  // ===================== MOVE HASH UPDATES =====================
  getMoveUpdate(position, move) {
    const updates = {
      piece: [],
      castling: null,
      ep: null,
      side: true
    };
    
    const color = position.side;
    const them = color ^ 1;
    
    // Moving piece
    updates.piece.push({
      color,
      piece: move.piece,
      square: move.from,
      operation: 'toggle'
    });
    
    updates.piece.push({
      color,
      piece: move.piece,
      square: move.to,
      operation: 'toggle'
    });
    
    // Handle captures
    if (move.flags === this.MOVE_FLAGS.CAPTURE || move.flags === this.MOVE_FLAGS.ENPASSANT) {
      let capturedSquare = move.to;
      let capturedPiece = move.captured;
      
      if (move.flags === this.MOVE_FLAGS.ENPASSANT) {
        capturedSquare = move.to + (color === this.COLORS.WHITE ? -8 : 8);
        capturedPiece = this.PIECE_TYPES.PAWN;
      }
      
      updates.piece.push({
        color: them,
        piece: capturedPiece,
        square: capturedSquare,
        operation: 'toggle'
      });
    }
    
    // Handle promotions
    if (move.flags === this.MOVE_FLAGS.PROMOTION) {
      // Remove pawn from destination
      updates.piece.push({
        color,
        piece: this.PIECE_TYPES.PAWN,
        square: move.to,
        operation: 'toggle'
      });
      
      // Add promoted piece
      updates.piece.push({
        color,
        piece: move.promotion,
        square: move.to,
        operation: 'toggle'
      });
    }
    
    // Handle castling
    if (move.flags === this.MOVE_FLAGS.CASTLING) {
      const rookFrom = move.extra1;
      const rookTo = move.extra2;
      
      updates.piece.push({
        color,
        piece: this.PIECE_TYPES.ROOK,
        square: rookFrom,
        operation: 'toggle'
      });
      
      updates.piece.push({
        color,
        piece: this.PIECE_TYPES.ROOK,
        square: rookTo,
        operation: 'toggle'
      });
    }
    
    // Castling rights update
    const castlingUpdate = this.getCastlingUpdate(position, move);
    if (castlingUpdate) {
      updates.castling = {
        old: position.castling,
        new: position.castling & ~castlingUpdate
      };
    }
    
    // En passant update
    if (position.epSquare >= 0) {
      updates.ep = {
        old: position.epSquare,
        new: -1
      };
    }
    
    // New en passant square
    if (move.piece === this.PIECE_TYPES.PAWN && Math.abs(move.to - move.from) === 16) {
      const epSquare = move.from + (color === this.COLORS.WHITE ? 8 : -8);
      updates.ep = {
        old: -1,
        new: epSquare
      };
    }
    
    return updates;
  }

  getCastlingUpdate(position, move) {
    let update = 0;
    const color = position.side;
    const kingSide = color === this.COLORS.WHITE ? 0b0001 : 0b0100;
    const queenSide = color === this.COLORS.WHITE ? 0b0010 : 0b1000;
    
    // King moved
    if (move.piece === this.PIECE_TYPES.KING) {
      update |= kingSide | queenSide;
    }
    // Rook moved
    else if (move.piece === this.PIECE_TYPES.ROOK) {
      if (move.from === (color === this.COLORS.WHITE ? 0 : 56)) update |= queenSide;
      if (move.from === (color === this.COLORS.WHITE ? 7 : 63)) update |= kingSide;
    }
    // Rook captured
    else if (position.castling) {
      if (move.to === (color === this.COLORS.WHITE ? 0 : 56)) update |= queenSide;
      if (move.to === (color === this.COLORS.WHITE ? 7 : 63)) update |= kingSide;
    }
    
    return update;
  }

  // ===================== INCREMENTAL UPDATE =====================
  applyUpdates(hash, updates) {
    // Apply piece updates
    for (const update of updates.piece) {
      hash = this.updatePieceHash(
        hash,
        update.color,
        update.piece,
        update.square
      );
    }
    
    // Apply castling update
    if (updates.castling) {
      hash = this.updateCastlingHash(hash, updates.castling.old);
      hash = this.updateCastlingHash(hash, updates.castling.new);
    }
    
    // Apply en passant update
    if (updates.ep) {
      if (updates.ep.old >= 0) {
        hash = this.updateEnPassantHash(hash, updates.ep.old);
      }
      if (updates.ep.new >= 0) {
        hash = this.updateEnPassantHash(hash, updates.ep.new);
      }
    }
    
    // Apply side update
    if (updates.side) {
      hash = this.updateSideHash(hash);
    }
    
    return hash;
  }

  // ===================== UTILITY METHODS =====================
  getPieceKey(color, piece, square) {
    return this.keys.pieces[color][piece - 1][square];
  }

  getCastlingKey(castlingRights) {
    return this.keys.castling[castlingRights];
  }

  getSideKey() {
    return this.keys.side;
  }

  // ===================== SERIALIZATION =====================
  serialize() {
    return {
      pieces: this.keys.pieces,
      side: this.keys.side,
      castling: this.keys.castling,
      ep: this.keys.ep
    };
  }

  deserialize(data) {
    this.keys = {
      pieces: data.pieces,
      side: data.side,
      castling: data.castling,
      ep: data.ep
    };
  }
}

export default Zobrist;
/////////////////////////////
// ===================== SEARCH MODULE =====================
// Implements the core search algorithms including alpha-beta pruning,
// iterative deepening, and various search optimizations

import MoveOrdering from './MoveOrdering.js';
import SearchExtensions from './SearchExtensions.js';
import ProbCut from './ProbCut.js';
import TimeManager from './TimeManager.js';

class Search {
  constructor(gameState) {
    this.gameState = gameState;
    
    // Search parameters
    this.MAX_DEPTH = 64;
    this.MAX_NODES = 1e9;
    this.MATE_VALUE = 32000;
    this.MATE_SCORE = this.MATE_VALUE - 1000;
    this.INFINITY = 1000000;
    
    // Search components
    this.moveOrdering = new MoveOrdering(this);
    this.extensions = new SearchExtensions(this);
    this.probCut = new ProbCut(this);
    this.timeManager = new TimeManager(this);
    
    // Search state
    this.nodes = 0;
    this.seldepth = 0;
    this.stopSearch = false;
    this.pvTable = Array(this.MAX_DEPTH).fill().map(() => []);
    this.killers = Array.from({length: 2}, () => new Array(this.MAX_DEPTH).fill(null));
    
    // Statistics
    this.cutoffs = {
      nullMove: 0,
      probCut: 0,
      futility: 0,
      lmr: 0,
      history: 0
    };
  }

  // ===================== MAIN SEARCH INTERFACE =====================
  async getBestMove(options = {}) {
    // Initialize search
    this.timeManager.init(options);
    this.resetSearchState();
    
    // Check for immediate termination conditions
    if (this.gameState.isDrawn()) {
      return this.gameState.MOVE_NONE;
    }

    // Probe opening book
    const bookMove = this.getBookMove();
    if (bookMove) return bookMove;

    // Check tablebases
    const tbMove = this.probeTablebases();
    if (tbMove) return tbMove;

    // Main search loop
    let bestMove = null;
    let bestScore = -this.INFINITY;
    let aspirationWindow = 25; // Initial window size

    for (let depth = 1; depth <= this.MAX_DEPTH; depth++) {
      let alpha = Math.max(-this.INFINITY, bestScore - aspirationWindow);
      let beta = Math.min(this.INFINITY, bestScore + aspirationWindow);

      // Aspiration window loop
      while (true) {
        const score = await this.search(depth, alpha, beta, false, true);

        // Adjust aspiration window
        if (score <= alpha) {
          alpha = Math.max(-this.INFINITY, alpha - aspirationWindow);
          beta = (alpha + beta) / 2;
          aspirationWindow *= 2;
        } else if (score >= beta) {
          beta = Math.min(this.INFINITY, beta + aspirationWindow);
          aspirationWindow *= 2;
        } else {
          bestScore = score;
          bestMove = this.pvTable[0][0];
          break;
        }

        // Check time after each iteration
        if (this.timeManager.shouldStop(this.nodes, depth)) {
          break;
        }
      }

      // Early exit conditions
      if (this.stopSearch || 
          Math.abs(bestScore) >= this.MATE_SCORE ||
          this.timeManager.shouldStop(this.nodes, depth)) {
        break;
      }

      aspirationWindow = Math.min(50, aspirationWindow * 1.5);
    }

    return bestMove || this.gameState.generateMoves()[0];
  }

  // ===================== CORE SEARCH ALGORITHM =====================
  async search(depth, alpha, beta, cutNode, isPvNode) {
    // Check termination conditions
    if (this.stopSearch) return alpha;
    if (this.gameState.isDrawn()) return this.gameState.getDynamicContempt();
    
    // QSearch at leaf nodes
    if (depth <= 0) {
      return this.qSearch(alpha, beta);
    }

    // TT probe
    const ttEntry = this.probeTT();
    const ttMove = ttEntry?.move || null;
    const ttScore = ttEntry?.score || -this.INFINITY;

    // TT cutoff
    if (!isPvNode && ttEntry && ttEntry.depth >= depth) {
      if (ttEntry.flag === 0) return ttScore;
      if (ttEntry.flag === 1 && ttScore >= beta) return beta;
      if (ttEntry.flag === 2 && ttScore <= alpha) return alpha;
    }

    // Check extension
    const inCheck = this.gameState.isInCheck();
    const extension = this.extensions.getExtension(depth, ttMove, inCheck);
    depth += extension;

    // Razoring
    if (!isPvNode && !inCheck && depth <= 3) {
      const eval = this.gameState.evaluate();
      if (eval + 125 * depth <= alpha) {
        return this.qSearch(alpha, beta);
      }
    }

    // Null move pruning
    if (!isPvNode && !inCheck && depth >= 2 && this.gameState.hasNonPawns()) {
      const R = 3 + Math.min(3, depth / 6);
      
      this.gameState.makeNullMove();
      const nullScore = -await this.search(depth - R, -beta, -beta + 1, true);
      this.gameState.undoNullMove();

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
    const moves = this.gameState.generateMoves();
    if (moves.length === 0) {
      return inCheck ? -this.MATE_VALUE + this.gameState.ply : this.gameState.getDynamicContempt();
    }

    this.moveOrdering.orderMoves(moves, ttMove, depth, isPvNode);

    // Main search loop
    let bestScore = -this.INFINITY;
    let bestMove = moves[0];
    let legalMoves = 0;
    const improving = !inCheck && this.gameState.evaluate() > 
      (this.gameState.stack.length >= 2 ? this.gameState.stack[this.gameState.stack.length - 2].staticEval : -this.INFINITY);

    for (let i = 0; i < moves.length; i++) {
      const move = moves[i];

      // Futility pruning
      if (!isPvNode && !inCheck && depth <= 7 && !move.captured && !move.promotion) {
        const margin = 150 + 175 * depth;
        if (this.gameState.evaluate() + margin <= alpha) {
          this.cutoffs.futility++;
          continue;
        }
      }

      // Late move pruning
      if (!isPvNode && !inCheck && depth <= 8 && legalMoves >= this.moveOrdering.lmpTable[depth][improving ? 1 : 0]) {
        continue;
      }

      // Make move and search
      const undo = this.gameState.makeMove(move);
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

      this.gameState.undoMove(move, undo);

      // Beta cutoff
      if (score >= beta) {
        this.moveOrdering.updateHistory(move, depth, beta - alpha);

        if (!move.captured && !move.promotion) {
          this.updateKillers(move, depth);
        }

        this.storeTT(depth, beta, 1, move, isPvNode);
        return beta;
      }

      // Update best score
      if (score > bestScore) {
        bestScore = score;
        bestMove = move;
        if (score > alpha) {
          alpha = score;
          this.updatePV(move, depth);
        }
      }

      legalMoves++;
    }

    // Store results in TT
    const flag = bestScore > alpha ? 0 : 2;
    this.storeTT(depth, bestScore, flag, bestMove, isPvNode);

    return bestScore;
  }

  // ===================== QUISCENCE SEARCH =====================
  qSearch(alpha, beta) {
    const standPat = this.gameState.evaluate();
    if (standPat >= beta) return beta;
    if (standPat > alpha) alpha = standPat;

    // Delta pruning
    const deltaMargin = 75 + 150 * (this.gameState.gamePhase() / 256);
    if (standPat + deltaMargin < alpha) {
      return alpha;
    }

    // Generate captures
    const moves = this.gameState.generateMoves().filter(move => {
      return move.captured || 
            (move.flags === this.gameState.MOVE_FLAGS.PROMOTION && this.gameState.see(move, -50));
    });

    // Sort moves using SEE
    moves.sort((a, b) => {
      const aValue = this.gameState.see(a, 0) + (a.captured ? this.gameState.pieceValue(a.captured) * 10 : 0);
      const bValue = this.gameState.see(b, 0) + (b.captured ? this.gameState.pieceValue(b.captured) * 10 : 0);
      return bValue - aValue;
    });

    // Search captures
    for (const move of moves) {
      // SEE pruning
      if (this.gameState.see(move, -25 - Math.abs(standPat - alpha))) {
        continue;
      }

      const undo = this.gameState.makeMove(move);
      const score = -this.qSearch(-beta, -alpha);
      this.gameState.undoMove(move, undo);

      if (score >= beta) return beta;
      if (score > alpha) alpha = score;
    }

    return alpha;
  }

  // ===================== HELPER METHODS =====================
  updatePV(move, depth) {
    this.pvTable[depth] = [move];
    if (depth > 0 && this.pvTable[depth - 1].length > 0) {
      this.pvTable[depth] = this.pvTable[depth].concat(this.pvTable[depth - 1]);
    }
  }

  updateKillers(move, depth) {
    if (!this.isSameMove(move, this.killers[0][depth])) {
      this.killers[1][depth] = this.killers[0][depth];
      this.killers[0][depth] = move;
    }
  }

  isSameMove(a, b) {
    return a && b && a.from === b.from && a.to === b.to && 
           (!a.promotion || a.promotion === b.promotion);
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
    this.pvTable.forEach(pv => pv.length = 0);
  }

  // ===================== TRANSPOSITION TABLE =====================
  initTranspositionTable(sizeMB = 128) {
    const sizeEntries = Math.floor((sizeMB * 1024 * 1024) / 24);
    this.transpositionTable = new Array(sizeEntries);
    this.ttMask = sizeEntries - 1;
    this.ttGeneration = 0;
  }

  probeTT() {
    const entry = this.transpositionTable[this.gameState.hash & this.ttMask];
    if (entry && entry.hash === this.gameState.hash) {
      return entry;
    }
    return null;
  }

  storeTT(depth, score, flag, move, isPvNode) {
    const index = this.gameState.hash & this.ttMask;
    const entry = {
      hash: this.gameState.hash,
      depth,
      score,
      flag,
      move,
      generation: this.ttGeneration,
      pvNode: isPvNode
    };
    
    // Always replace in PV nodes, or if depth is better
    if (!this.transpositionTable[index] || 
        isPvNode || 
        entry.depth > this.transpositionTable[index].depth ||
        entry.generation !== this.transpositionTable[index].generation) {
      this.transpositionTable[index] = entry;
    }
  }

  // ===================== OPENING BOOK & TABLEBASES =====================
  getBookMove() {
    // Implementation would connect to opening book
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


    
    
    return null;
  }

  probeTablebases() {
    // Implementation would connect to tablebase
    
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



    
    return null;
  }

  // ===================== UTILITY METHODS =====================
  getSearchInfo() {
    return {
      depth: this.pvTable.findIndex(pv => pv.length === 0) - 1,
      seldepth: this.seldepth,
      nodes: this.nodes,
      time: this.timeManager.elapsed(),
      nps: Math.floor(this.nodes / (this.timeManager.elapsed() / 1000)) || 0,
      pv: this.pvTable[0]?.map(m => this.moveToUCI(m)).join(' ') || '',
      score: this.lastScore,
      hashfull: Math.floor((this.transpositionTable.filter(e => e?.generation === this.ttGeneration).length / this.ttMask) * 1000),
      tbhits: 0 // Would be updated by tablebase probes
    };
  }

  moveToUCI(move) {
    const files = 'abcdefgh';
    const ranks = '12345678';
    const fromFile = files[move.from % 8];
    const fromRank = ranks[Math.floor(move.from / 8)];
    const toFile = files[move.to % 8];
    const toRank = ranks[Math.floor(move.to / 8)];
    
    let uci = fromFile + fromRank + toFile + toRank;
    if (move.promotion) {
      const promoPieces = ['', 'n', 'b', 'r', 'q'];
      uci += promoPieces[move.promotion];
    }
    
    return uci;
  }
}

export default Search;
/////////////////////////////////
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

///////////////////////////
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
/////////////////////////////////
// search/MoveOrdering.js

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

  clear() {
    // Clear history tables
    this.historyHeuristic.fill(0);
    this.butterfly.fill(0);
    
    // Clear killer moves
    for (let i = 0; i < this.killers.length; i++) {
      for (let j = 0; j < this.killers[i].length; j++) {
        this.killers[i][j] = null;
      }
    }
    
    // Clear counter and follow-up moves
    for (let i = 0; i < this.counterMoves.length; i++) {
      for (let j = 0; j < this.counterMoves[i].length; j++) {
        this.counterMoves[i][j] = null;
      }
    }
    
    for (let i = 0; i < this.followupMoves.length; i++) {
      for (let j = 0; j < this.followupMoves[i].length; j++) {
        this.followupMoves[i][j] = null;
      }
    }
  }
}

export default MoveOrdering;
/////////////////////////////
// search/Extensions.js
class SearchExtensions {
  constructor(engine) {
    this.engine = engine;
    
    // Extension constants
    this.MAX_EXTENSIONS = 2;
    this.SINGULAR_EXTENSION_DEPTH = 8;
    this.SINGULAR_MARGIN = 85;
    this.CHECK_EXTENSION = 1;
    this.PV_EXTENSION = 1;
    this.PASSED_PAWN_EXTENSION = 1;
    this.RECAPTURE_EXTENSION = 1;
    
    // History table for extensions [depth][moveKey]
    this.extensionHistory = new Map();
    
    // Statistics
    this.stats = {
      totalExtensions: 0,
      checkExtensions: 0,
      singularExtensions: 0,
      passedPawnExtensions: 0,
      recaptureExtensions: 0,
      pvExtensions: 0
    };
  }

  /**
   * Determine if a move should be extended
   * @param {Object} position - Current board position
   * @param {Object} move - Move being considered
   * @param {number} depth - Current search depth
   * @param {number} alpha - Alpha bound
   * @param {number} beta - Beta bound
   * @param {boolean} isPVNode - Whether this is a PV node
   * @returns {number} Number of extensions to apply (0, 1, or 2)
   */
  getExtension(position, move, depth, alpha, beta, isPVNode) {
    let extension = 0;
    
    // 1. Check extension (always extend checks)
    if (position.isInCheck()) {
      extension = this.CHECK_EXTENSION;
      this.stats.checkExtensions++;
    }
    
    // 2. Singular extension (critical moves)
    if (extension === 0 && 
        depth >= this.SINGULAR_EXTENSION_DEPTH && 
        this.isSingularMove(position, move, depth, alpha, beta)) {
      extension = this.SINGULAR_EXTENSION;
      this.stats.singularExtensions++;
    }
    
    // 3. Passed pawn push extension
    if (extension === 0 && this.isPassedPawnPush(move)) {
      extension = this.PASSED_PAWN_EXTENSION;
      this.stats.passedPawnExtensions++;
    }
    
    // 4. Recapture extension
    if (extension === 0 && this.isRecapture(move)) {
      extension = this.RECAPTURE_EXTENSION;
      this.stats.recaptureExtensions++;
    }
    
    // 5. PV extension (extend PV nodes in shallow depths)
    if (extension === 0 && isPVNode && depth <= 6) {
      extension = this.PV_EXTENSION;
      this.stats.pvExtensions++;
    }
    
    // Cap at maximum extensions
    extension = Math.min(extension, this.MAX_EXTENSIONS);
    
    if (extension > 0) {
      this.stats.totalExtensions++;
      this.recordExtension(depth, move, extension);
    }
    
    return extension;
  }

  /**
   * Check if a move is singular (significantly better than alternatives)
   */
  isSingularMove(position, move, depth, alpha, beta) {
    // Skip if not deep enough or no TT entry
    if (depth < this.SINGULAR_EXTENSION_DEPTH) return false;
    
    const ttEntry = position.probeTT();
    if (!ttEntry || ttEntry.depth < depth - 3) return false;

    // Don't extend if this is the TT move
    if (ttEntry.move && ttEntry.move.from === move.from && ttEntry.move.to === move.to) {
      return false;
    }
    
    // Singular beta margin
    const singularBeta = Math.max(
      ttEntry.score - this.getSingularMargin(depth),
      -position.MATE_VALUE
    );
    
    // Multi-phase verification:
    
    // Phase 1: Null move verification
    if (depth >= 10 && !position.isInCheck()) {
      position.makeNullMove();
      const nullScore = -position.search(
        Math.floor(depth / 2) - 1, 
        -singularBeta, 
        -singularBeta + 1, 
        false
      );
      position.undoNullMove();
      
      if (nullScore >= singularBeta) return false;
    }
    
    // Phase 2: Static exchange evaluation for captures
    if (move.captured && position.see(move) < 0) {
      return false;
    }
    
    // Phase 3: Full verification search
    const undo = position.makeMove(move);
    const score = -position.search(
      depth - this.getReduction(depth) - 1,
      -singularBeta,
      -singularBeta + 1,
      false
    );
    position.undoMove(move, undo);
    
    return score < singularBeta - this.SINGULAR_MARGIN;
  }

  /**
   * Check if move is a passed pawn push
   */
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

  /**
   * Check if move is a recapture
   */
  isRecapture(move) {
    if (!move || !move.captured) return false;
    
    // Check if this is recapturing the opponent's last moved piece
    if (this.engine.stack.length < 1) return false;
    
    const lastMove = this.engine.stack[this.engine.stack.length - 1].move;
    return lastMove && move.to === lastMove.to;
  }

  /**
   * Record successful extensions in history
   */
  recordExtension(depth, move, extension) {
    const moveKey = this.getMoveKey(move);
    const depthKey = Math.min(depth, 20); // Cap depth for history
    
    if (!this.extensionHistory.has(depthKey)) {
      this.extensionHistory.set(depthKey, new Map());
    }
    
    const depthMap = this.extensionHistory.get(depthKey);
    depthMap.set(moveKey, (depthMap.get(moveKey) || 0) + extension);
  }

  /**
   * Check if a move has been frequently extended before
   */
  hasHistoryOfExtensions(depth, move) {
    const moveKey = this.getMoveKey(move);
    const depthKey = Math.min(depth, 20);
    
    if (!this.extensionHistory.has(depthKey)) return false;
    
    const count = this.extensionHistory.get(depthKey).get(moveKey) || 0;
    return count > 2; // Only if extended multiple times before
  }

  /**
   * Create a unique key for a move
   */
  getMoveKey(move) {
    return (move.from << 16) | (move.to << 8) | move.piece;
  }

  /**
   * Clear history between searches
   */
  clearHistory() {
    this.extensionHistory.clear();
    this.stats = {
      totalExtensions: 0,
      checkExtensions: 0,
      singularExtensions: 0,
      passedPawnExtensions: 0,
      recaptureExtensions: 0,
      pvExtensions: 0
    };
  }

  /**
   * Get dynamic singular margin based on depth
   */
  getSingularMargin(depth) {
    // Base margin increases with depth
    let margin = this.SINGULAR_MARGIN * depth / 8;
    
    // Adjust for game phase
    const phase = this.engine.gamePhase() / 256;
    if (phase > 0.7) { // Endgame
      margin *= 1.3;
    }
    
    return Math.floor(margin);
  }

  /**
   * Get reduction for verification search
   */
  getReduction(depth) {
    const baseReduction = 3;
    // Increase reduction at higher depths
    return Math.min(baseReduction + Math.floor(depth / 6), 6);
  }

  /**
   * Get statistics about extensions
   */
  getStatistics() {
    return {
      ...this.stats,
      extensionHistorySize: Array.from(this.extensionHistory.values())
        .reduce((sum, map) => sum + map.size, 0)
    };
  }
}

export default SearchExtensions;
///////////////////////////////
// search/Reductions.js
class SearchReductions {
  constructor(engine) {
    this.engine = engine;
    
    // Reduction constants
    this.BASE_REDUCTION = 0.85;
    this.MAX_REDUCTION = 3;
    this.NULL_MOVE_R = 2; // Base null move reduction
    this.LMR_DEPTH = 3;   // Minimum depth for LMR
    this.LMR_MOVE_COUNT = 3; // Move count threshold for LMR
    
    // Reduction tables [depth][moveNumber]
    this.reductionTable = Array(64).fill().map(() => new Array(64).fill(0));
    this.initReductionTable();
    
    // History heuristics
    this.historyReductions = new Map();
    
    // Statistics
    this.stats = {
      totalReductions: 0,
      lmrReductions: 0,
      nullMoveReductions: 0,
      futilityReductions: 0,
      historyPrunings: 0,
      lateMovePrunings: 0
    };
  }

  /**
   * Initialize the reduction lookup table
   */
  initReductionTable() {
    for (let depth = 1; depth < 64; depth++) {
      for (let moveNum = 1; moveNum < 64; moveNum++) {
        // Base reduction formula
        let reduction = this.BASE_REDUCTION + Math.log(depth) * Math.log(moveNum) / 2.1;
        
        // Cap at maximum reduction
        reduction = Math.min(reduction, this.MAX_REDUCTION);
        
        // Store rounded value
        this.reductionTable[depth][moveNum] = Math.round(reduction * 100) / 100;
      }
    }
  }

  /**
   * Get late move reduction (LMR) for a move
   */
  getLMR(depth, moveNumber, improving, move) {
    if (depth < this.LMR_DEPTH || moveNumber < this.LMR_MOVE_COUNT) {
      return 0;
    }
    
    // Base reduction from table
    let reduction = this.reductionTable[Math.min(depth, 63)][Math.min(moveNumber, 63)];
    
    // Adjust based on move characteristics
    if (!improving) reduction += 0.5;
    if (move.captured || move.promotion) reduction = 0;
    
    // History-based adjustment
    const history = this.getHistoryScore(move);
    if (history < 0) {
      reduction += Math.min(0.5, -history / 20000);
    }
    
    // Cap reduction
    reduction = Math.max(0, Math.min(depth - 1, reduction));
    
    if (reduction > 0) {
      this.stats.lmrReductions++;
      this.stats.totalReductions++;
    }
    
    return reduction;
  }

  /**
   * Get null move reduction (NMR)
   */
  getNullMoveReduction(depth, eval, beta) {
    // Don't reduce if in check or in endgame
    if (this.engine.isInCheck() || !this.engine.hasNonPawns()) {
      return 0;
    }
    
    // Dynamic null move reduction based on depth and evaluation
    let R = this.NULL_MOVE_R + Math.min(3, Math.floor(depth / 6));
    
    // Increase reduction when ahead
    if (eval > beta + 150) {
      R += 1;
    }
    
    // Decrease reduction in pawn endgames
    if (this.engine.isPawnEndgame()) {
      R = Math.max(1, R - 1);
    }
    
    this.stats.nullMoveReductions++;
    this.stats.totalReductions++;
    
    return R;
  }

  /**
   * Check if futility reduction applies
   */
  isFutile(depth, eval, alpha, move) {
    // Only apply at shallow depths for quiet moves
    if (depth > 6 || move.captured || move.promotion) {
      return false;
    }
    
    // Futility margin based on depth
    const margin = 100 + 150 * depth;
    
    // If eval is below alpha by margin, consider futile
    if (eval + margin <= alpha) {
      this.stats.futilityReductions++;
      this.stats.totalReductions++;
      return true;
    }
    
    return false;
  }

  /**
   * Check if move can be pruned based on history
   */
  isHistoryPrunable(move, depth) {
    if (depth > 4 || move.captured || move.promotion) {
      return false;
    }
    
    const historyScore = this.getHistoryScore(move);
    const threshold = depth * depth * 2;
    
    if (historyScore < threshold) {
      this.stats.historyPrunings++;
      return true;
    }
    
    return false;
  }

  /**
   * Check if move can be pruned as late move
   */
  isLateMovePrunable(depth, moveNumber, improving) {
    if (depth > 8 || moveNumber < 10) {
      return false;
    }
    
    // LMP table [depth][improving]
    const lmpTable = [
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
    
    const maxMoves = lmpTable[Math.min(depth, 8)][improving ? 1 : 0];
    if (moveNumber >= maxMoves) {
      this.stats.lateMovePrunings++;
      return true;
    }
    
    return false;
  }

  /**
   * Get history score for a move
   */
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

  /**
   * Update history reductions
   */
  updateHistory(move, depth, bonus) {
    const from = move.from;
    const to = move.to;
    const piece = move.piece;
    const color = this.engine.side;
    const index = color * 49152 + from * 768 + piece * 64 + to;
    
    // Update history heuristic
    this.engine.historyHeuristic[index] += depth * depth * Math.min(10, bonus);
    
    // Keep history within bounds
    this.engine.historyHeuristic[index] = Math.max(
      -2000000,
      Math.min(2000000, this.engine.historyHeuristic[index])
    );
  }

  /**
   * Clear history between searches
   */
  clearHistory() {
    this.historyReductions.clear();
    this.stats = {
      totalReductions: 0,
      lmrReductions: 0,
      nullMoveReductions: 0,
      futilityReductions: 0,
      historyPrunings: 0,
      lateMovePrunings: 0
    };
  }

  /**
   * Get statistics about reductions
   */
  getStatistics() {
    return {
      ...this.stats,
      reductionTable: this.reductionTable,
      historySize: this.historyReductions.size
    };
  }
}

export default SearchReductions;
//////////////////////////////
// search/TimeManagement.js
class TimeManagement {
  constructor(engine) {
    this.engine = engine;
    
    // Time control parameters
    this.timeBudget = 0;       // Total time allocated for current move
    this.panicTime = 0;        // Time threshold for panic mode
    this.maxNodes = Infinity;  // Maximum nodes to search
    this.startTime = 0;        // When the current search started
    
    // Dynamic adjustment factors
    this.OPTIMAL_TIME_FACTOR = 0.7;  // Ideal portion of time to use
    this.PANIC_TIME_FACTOR = 0.1;    // Portion for panic threshold
    this.MAX_TIME_FACTOR = 0.95;     // Maximum portion of remaining time
    this.MIN_TIME_MS = 50;           // Minimum time per move
    
    // Search state tracking
    this.lastScore = 0;        // Score from previous iteration
    this.scoreDrops = 0;       // Number of consecutive score drops
    this.bestMoveChanges = 0;  // Count of best move changes
    this.lastBestMove = null;  // Previous best move
    this.pvStability = 0;      // Measure of PV stability
    
    // Time control history
    this.moveTimeHistory = [];
    this.maxHistorySize = 20;
  }

  /**
   * Initialize time management for a new search
   * @param {Object} options - Time control options
   * @param {number} options.wtime - White time remaining (ms)
   * @param {number} options.btime - Black time remaining (ms)
   * @param {number} options.winc - White increment per move (ms)
   * @param {number} options.binc - Black increment per move (ms)
   * @param {number} options.movestogo - Moves remaining to time control
   * @param {number} options.movetime - Fixed time per move (ms)
   * @param {number} options.depth - Fixed depth search
   * @param {number} options.nodes - Fixed node search
   * @param {boolean} options.infinite - Infinite search flag
   */
  init(options) {
    this.startTime = Date.now();
    
    // Handle special search modes
    if (options.infinite || options.depth || options.nodes) {
      this.timeBudget = Infinity;
      this.panicTime = Infinity;
      this.maxNodes = options.nodes || Infinity;
      return;
    }

    // Handle fixed time per move
    if (options.movetime) {
      this.timeBudget = options.movetime;
      this.panicTime = Math.min(
        options.movetime * this.PANIC_TIME_FACTOR,
        options.btime ? options.btime * 0.1 : options.wtime * 0.1
      );
      return;
    }

    // Calculate time based on game situation
    const timeLeft = this.engine.side === this.engine.COLORS.WHITE ? 
      options.wtime : options.btime;
    const increment = this.engine.side === this.engine.COLORS.WHITE ? 
      options.winc : options.binc;
    const movesToGo = options.movestogo || this.estimateMovesToGo();

    // Base time calculation with increment
    let baseTime = timeLeft / movesToGo + increment * 0.8;
    
    // Adjust for game phase (spend more time in complex positions)
    const phase = this.engine.gamePhase() / 256;
    baseTime *= (1.3 - phase * 0.4); // More time in middlegame
    
    // Adjust for material imbalance
    const materialDiff = Math.abs(this.engine.evaluate());
    baseTime *= (1.0 + Math.min(0.5, materialDiff / 800));
    
    // Adjust for position complexity
    baseTime *= (1.0 + this.calculateComplexity() * 0.5);
    
    // Final time budget with safety limits
    this.timeBudget = Math.max(
      this.MIN_TIME_MS,
      Math.min(timeLeft * this.MAX_TIME_FACTOR, baseTime * this.OPTIMAL_TIME_FACTOR)
    );
    
    // Set panic threshold
    this.panicTime = Math.min(timeLeft * 0.1, this.timeBudget * 0.2);
    
    // Node limit based on time control
    this.maxNodes = timeLeft < 30000 ? 1e6 : 5e6;
    
    // Reset tracking variables
    this.resetSearchTracking();
    
    // Record move time history
    this.recordMoveTime();
  }

  /**
   * Determine if search should stop
   * @param {number} nodes - Nodes searched so far
   * @param {number} depth - Current search depth
   * @returns {boolean} True if search should stop
   */
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
    const currentBestMove = this.engine.pvTable[0]?.[0];
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

  /**
   * Estimate number of moves remaining to time control
   */
  estimateMovesToGo() {
    const phase = this.engine.gamePhase() / 256;
    const material = this.engine.evaluate();
    
    // Fewer moves in endgame, more in imbalanced positions
    let movesToGo = 30 - phase * 10;
    
    // Adjust for material imbalance
    if (Math.abs(material) > 300) {
      movesToGo -= 5;
    }
    
    // Adjust for time remaining
    const timeLeft = this.engine.side === this.engine.COLORS.WHITE ? 
      this.engine.wtime : this.engine.btime;
    if (timeLeft < 30000) {
      movesToGo = Math.max(10, movesToGo - 5);
    }
    
    return Math.max(10, Math.min(40, movesToGo));
  }

  /**
   * Calculate position complexity
   */
  calculateComplexity() {
    let complexity = 0;
    
    // Material imbalance
    const materialDiff = Math.abs(this.engine.evaluate());
    complexity += Math.min(0.3, materialDiff / 500);
    
    // Pawn structure
    complexity += Math.min(0.4, Math.abs(this.engine.evaluatePawnStructure()) / 200);
    
    // Mobility
    complexity += Math.min(0.3, Math.abs(this.engine.evaluateMobility()) / 150);
    
    // King safety
    complexity += Math.min(0.4, Math.abs(this.engine.evaluateKingSafety()) / 100);
    
    return Math.min(1, complexity);
  }

  /**
   * Record move time for adaptive time management
   */
  recordMoveTime() {
    const lastMoveTime = this.moveTimeHistory[this.moveTimeHistory.length - 1];
    const currentEstimate = this.timeBudget;
    
    // Don't record if we're using fixed time
    if (lastMoveTime && Math.abs(lastMoveTime - currentEstimate) < 100) {
      return;
    }
    
    this.moveTimeHistory.push(currentEstimate);
    if (this.moveTimeHistory.length > this.maxHistorySize) {
      this.moveTimeHistory.shift();
    }
  }

  /**
   * Get average move time from history
   */
  getAverageMoveTime() {
    if (this.moveTimeHistory.length === 0) return 0;
    return this.moveTimeHistory.reduce((sum, time) => sum + time, 0) / 
           this.moveTimeHistory.length;
  }

  /**
   * Reset search tracking variables
   */
  resetSearchTracking() {
    this.lastScore = 0;
    this.scoreDrops = 0;
    this.bestMoveChanges = 0;
    this.pvStability = 0;
    this.lastBestMove = null;
  }

  /**
   * Check if two moves are the same
   */
  isSameMove(a, b) {
    return a && b && 
           a.from === b.from && 
           a.to === b.to && 
           (!a.promotion || a.promotion === b.promotion);
  }

  /**
   * Get search info for UCI reporting
   */
  getSearchInfo() {
    const elapsed = Date.now() - this.startTime;
    return {
      time: elapsed,
      nodes: this.engine.nodes,
      depth: this.engine.seldepth,
      nps: Math.floor(this.engine.nodes / (elapsed / 1000)) || 0,
      score: this.engine.lastScore,
      pv: this.engine.pvTable[0]?.map(m => this.engine.moveToUCI(m)).join(' ') || '',
      hashfull: Math.floor((this.engine.transpositionTable.size / this.engine.ttSize) * 1000),
      tbhits: this.engine.syzygyHits || 0
    };
  }

  /**
   * Get remaining time budget
   */
  getRemainingTime() {
    return Math.max(0, this.timeBudget - (Date.now() - this.startTime));
  }
}

export default TimeManagement;
////////////////////////////////////
// evaluation/Material.js

class MaterialEvaluator {
  constructor(engine) {
    this.engine = engine;
    
    // Piece values [middlegame, endgame]
    this.PIECE_VALUES = [
      [0, 0],       // None
      [105, 140],   // Pawn
      [325, 370],   // Knight
      [345, 390],   // Bishop
      [550, 610],   // Rook
      [1020, 1080], // Queen
      [20000, 20000] // King (not actually used)
    ];
    
    // Bishop pair bonus [middlegame, endgame]
    this.BISHOP_PAIR = [30, 15];
    
    // Tempo bonus
    this.TEMPO_BONUS = 12;
  }

  /**
   * Evaluate material balance and special bonuses
   * @param {number} phaseFactor - 0 (middlegame) to 1 (endgame)
   * @returns {number} material score in centipawns
   */
  evaluate(phaseFactor) {
    let score = 0;
    
    // 1. Basic material count
    score += this.evaluatePieceMaterial(phaseFactor);
    
    // 2. Bishop pair bonus
    score += this.evaluateBishopPair(phaseFactor);
    
    // 3. Tempo bonus (small bonus for side to move)
    score += this.TEMPO_BONUS;
    
    return score;
  }

  /**
   * Evaluate standard piece material
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluatePieceMaterial(phaseFactor) {
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
    
    return score;
  }

  /**
   * Evaluate bishop pair bonus
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateBishopPair(phaseFactor) {
    let score = 0;
    
    // White bishop pair
    if (this.engine.popCount(
      this.engine.bitboards[this.engine.COLORS.WHITE * 6 + this.engine.PIECE_TYPES.BISHOP - 1]
    ) >= 2) {
      score += this.interpolateBishopPair(phaseFactor);
    }
    
    // Black bishop pair
    if (this.engine.popCount(
      this.engine.bitboards[this.engine.COLORS.BLACK * 6 + this.engine.PIECE_TYPES.BISHOP - 1]
    ) >= 2) {
      score -= this.interpolateBishopPair(phaseFactor);
    }
    
    return score;
  }

  /**
   * Interpolate between middlegame and endgame piece values
   * @param {number} piece 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  interpolateValue(piece, phaseFactor) {
    return this.PIECE_VALUES[piece][0] * (1 - phaseFactor) + 
           this.PIECE_VALUES[piece][1] * phaseFactor;
  }

  /**
   * Interpolate bishop pair bonus
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  interpolateBishopPair(phaseFactor) {
    return this.BISHOP_PAIR[0] * (1 - phaseFactor) + 
           this.BISHOP_PAIR[1] * phaseFactor;
  }

  /**
   * Get the value of a piece in the current game phase
   * @param {number} pieceType 
   * @returns {number} 
   */
  getPieceValue(pieceType) {
    const phase = this.engine.gamePhase() / 256;
    return this.interpolateValue(pieceType, phase);
  }

  /**
   * Get material imbalance between sides
   * @returns {number} positive if white has material advantage
   */
  getMaterialImbalance() {
    const phase = this.engine.gamePhase() / 256;
    let imbalance = 0;
    
    for (let piece = this.engine.PIECE_TYPES.PAWN; piece <= this.engine.PIECE_TYPES.QUEEN; piece++) {
      const whiteCount = this.engine.popCount(
        this.engine.bitboards[this.engine.COLORS.WHITE * 6 + piece - 1]
      );
      const blackCount = this.engine.popCount(
        this.engine.bitboards[this.engine.COLORS.BLACK * 6 + piece - 1]
      );
      
      imbalance += (whiteCount - blackCount) * this.interpolateValue(piece, phase);
    }
    
    return imbalance;
  }

  /**
   * Check if material is approximately balanced
   * @param {number} threshold - maximum allowed imbalance
   * @returns {boolean}
   */
  isMaterialBalanced(threshold = 100) {
    return Math.abs(this.getMaterialImbalance()) <= threshold;
  }
}

export default MaterialEvaluator;
///////////////////////////////
// evaluation/PieceSquare.js

class PieceSquareEvaluator {
  constructor(engine) {
    this.engine = engine;
    this.initTables();
  }

  /**
   * Initialize piece-square tables for all pieces
   */
  initTables() {
    // Piece-square tables [middlegame, endgame]
    this.TABLES = {
      [this.engine.PIECE_TYPES.PAWN]: {
        mg: [
           0,   0,   0,   0,   0,   0,   0,   0,
          98, 134,  61,  95,  68, 126,  34, -11,
          -6,   7,  26,  31,  65,  56,  25, -20,
         -14,  13,   6,  21,  23,  12,  17, -23,
         -27,  -2,  -5,  12,  17,   6,  10, -25,
         -26,  -4,  -4, -10,   3,   3,  33, -12,
         -35,  -1, -20, -23, -15,  24,  38, -22,
           0,   0,   0,   0,   0,   0,   0,   0
        ],
        eg: [
           0,   0,   0,   0,   0,   0,   0,   0,
         140, 140, 140, 140, 140, 140, 140, 140,
          90,  90,  90,  90,  90,  90,  90,  90,
          50,  50,  50,  50,  50,  50,  50,  50,
          20,  20,  20,  20,  20,  20,  20,  20,
           0,   0,   0,   0,   0,   0,   0,   0,
           0,   0,   0,   0,   0,   0,   0,   0,
           0,   0,   0,   0,   0,   0,   0,   0
        ]
      },
      [this.engine.PIECE_TYPES.KNIGHT]: {
        mg: [
        -167, -89, -34, -49,  61, -97, -15, -107,
         -73, -41,  72,  36,  23,  62,   7,  -17,
         -47,  60,  37,  65,  84, 129,  73,   44,
          -9,  17,  19,  53,  37,  69,  18,   22,
         -13,   4,  16,  13,  28,  19,  21,   -8,
         -23,  -9,  12,  10,  19,  17,  25,  -16,
         -29, -53, -12,  -3,  -1,  18, -14,  -19,
        -105, -21, -58, -33, -17, -28, -19,  -23
        ],
        eg: [
         -58, -38, -13, -28, -31, -27, -63, -99,
         -25,  -8, -25,  -2,  -9, -25, -24, -52,
         -24, -20,  10,   9,  -1,  -9, -19, -41,
         -17,   3,  22,  22,  22,  11,   8, -18,
         -18,  -6,  16,  25,  16,  17,   4, -18,
         -23,  -3,  -1,  15,  10,  -3, -20, -22,
         -42, -20, -10,  -5,  -2, -20, -23, -44,
         -29, -51, -23, -15, -22, -18, -50, -64
        ]
      },
      [this.engine.PIECE_TYPES.BISHOP]: {
        mg: [
         -29,   4, -82, -37, -25, -42,   7,  -8,
         -26,  16, -18, -13,  30,  59,  18, -47,
         -16,  37,  43,  40,  35,  50,  37,  -2,
          -4,   5,  19,  50,  37,  37,   7,  -2,
          -6,  13,  13,  26,  34,  12,  10,   4,
           0,  15,  15,  15,  14,  27,  18,  10,
           4,  15,  16,   0,   7,  21,  33,   1,
         -33,  -3, -14, -21, -13, -12, -39, -21
        ],
        eg: [
         -14, -21, -11,  -8, -7,  -9, -17, -24,
          -8,  -4,   7, -12, -3, -13,  -4, -14,
           2,  -8,   0,  -1, -2,   6,   0,   4,
          -3,   9,  12,   9, 14,  10,   3,   2,
          -6,   3,  13,  19,  7,  10,  -3,  -9,
         -12,  -3,   8,  10, 13,   3,  -7, -15,
         -14, -18,  -7,  -1,  4,  -9, -15, -27,
         -23,  -9, -23,  -5, -9, -16,  -5, -17
        ]
      },
      [this.engine.PIECE_TYPES.ROOK]: {
        mg: [
          32,  42,  32,  51,  63,   9,  31,  43,
          27,  32,  58,  62,  80,  67,  26,  44,
          -5,  19,  26,  36,  17,  45,  61,  16,
         -24, -11,   7,  26,  24,  35,  -8, -20,
         -36, -26, -12,  -1,   9,  -7,   6, -23,
         -45, -25, -16, -17,   3,   0,  -5, -33,
         -44, -16, -20,  -9,  -1,  11,  -6, -71,
         -19, -13,   1,  17,  16,   7, -37, -26
        ],
        eg: [
          13, 10, 18, 15, 12,  12,   8,   5,
          11, 13, 13, 11, -3,   3,   8,   3,
           7,  7,  7,  5,  4,  -3,  -5,  -3,
           4,  3, 13,  1,  2,   1,  -1,   2,
           3,  5,  8,  4, -5,  -6,  -8, -11,
          -4,  0, -5, -1, -7, -12,  -8, -16,
          -6, -6,  0,  2, -9,  -9, -11,  -3,
          -9,  2,  3, -1, -5, -13,   4, -20
        ]
      },
      [this.engine.PIECE_TYPES.QUEEN]: {
        mg: [
         -28,   0,  29,  12,  59,  44,  43,  45,
         -24, -39,  -5,   1, -16,  57,  28,  54,
         -13, -17,   7,   8,  29,  56,  47,  57,
         -27, -27, -16, -16,  -1,  17,  -2,   1,
          -9, -26,  -9, -10,  -2,  -4,   3,  -3,
         -14,   2, -11,  -2,  -5,   2,  14,   5,
         -35,  -8,  11,   2,   8,  15,  -3,   1,
          -1, -18,  -9,  10, -15, -25, -31, -50
        ],
        eg: [
         -9,  22,  22,  27,  27,  19,  10,  20,
         -17,  20,  32,  41,  58,  25,  30,   0,
         -20,   6,   9,  49,  47,  35,  19,   9,
           3,  22,  24,  45,  57,  40,  57,  36,
         -18,  28,  19,  47,  31,  34,  39,  23,
         -16, -27,  15,   6,   9,  17,  10,   5,
         -22, -23, -30, -16, -16, -23, -36, -32,
         -33, -28, -22, -43,  -5, -32, -20, -41
        ]
      },
      [this.engine.PIECE_TYPES.KING]: {
        mg: [
         -65,  23,  16, -15, -56, -34,   2,  13,
          29,  -1, -20,  -7,  -8,  -4, -38, -29,
          -9,  24,   2, -16, -20,   6,  22, -22,
         -17, -20, -12, -27, -30, -25, -14, -36,
         -49,  -1, -27, -39, -46, -44, -33, -51,
         -14, -14, -22, -46, -44, -30, -15, -27,
           1,   7,  -8, -64, -43, -16,   9,   8,
         -15,  36,  12, -54,   8, -28,  24,  14
        ],
        eg: [
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
    };
  }

  /**
   * Evaluate piece-square tables for both sides
   * @param {number} phaseFactor - 0 (middlegame) to 1 (endgame)
   * @returns {number} evaluation score in centipawns
   */
  evaluate(phaseFactor) {
    let score = 0;
    
    // Evaluate for each piece type and color
    for (let color = 0; color < 2; color++) {
      for (let piece = 0; piece < 6; piece++) {
        if (!this.TABLES[piece]) continue;
        
        const sign = color === this.engine.COLORS.WHITE ? 1 : -1;
        let bb = this.engine.bitboards[color * 6 + piece];
        
        while (bb) {
          const sq = this.engine.bitScanForward(bb);
          bb &= bb - 1n;
          
          // Get square value (mirror for black pieces)
          const tableSq = color === this.engine.COLORS.WHITE ? sq : 63 - sq;
          const mg = this.TABLES[piece].mg[tableSq];
          const eg = this.TABLES[piece].eg[tableSq];
          
          // Interpolate between middlegame and endgame values
          score += sign * (mg * (1 - phaseFactor) + eg * phaseFactor);
        }
      }
    }
    
    return score;
  }

  /**
   * Get the value of a piece on a specific square
   * @param {number} pieceType 
   * @param {number} square 
   * @param {number} color 
   * @returns {number} 
   */
  getSquareValue(pieceType, square, color) {
    const phase = this.engine.gamePhase() / 256;
    const tableSq = color === this.engine.COLORS.WHITE ? square : 63 - square;
    
    const mg = this.TABLES[pieceType].mg[tableSq];
    const eg = this.TABLES[pieceType].eg[tableSq];
    
    return mg * (1 - phase) + eg * phase;
  }

  /**
   * Get the best square for a piece type in the current phase
   * @param {number} pieceType 
   * @param {number} color 
   * @returns {number} best square index
   */
  getBestSquare(pieceType, color) {
    const phase = this.engine.gamePhase() / 256;
    const table = this.TABLES[pieceType];
    
    let bestScore = -Infinity;
    let bestSquare = 0;
    
    for (let sq = 0; sq < 64; sq++) {
      const tableSq = color === this.engine.COLORS.WHITE ? sq : 63 - sq;
      const score = table.mg[tableSq] * (1 - phase) + table.eg[tableSq] * phase;
      
      if (score > bestScore) {
        bestScore = score;
        bestSquare = sq;
      }
    }
    
    return bestSquare;
  }
}

export default PieceSquareEvaluator;
/////////////////////////////////////
// evaluation/PawnStructure.js

class PawnStructureEvaluator {
  constructor(engine) {
    this.engine = engine;
    
    // Penalties and bonuses
    this.DOUBLED_PENALTY = [-10, -20]; // [mg, eg]
    this.ISOLATED_PENALTY = [-15, -25]; // [mg, eg]
    this.BACKWARD_PENALTY = [-10, -15]; // [mg, eg]
    this.PASSED_BONUS = [10, 50]; // [mg, eg]
    this.CONNECTED_BONUS = [5, 15]; // [mg, eg]
    this.PHALANX_BONUS = [10, 20]; // [mg, eg]
    
    // Initialize masks
    this.initMasks();
    
    // Pawn hash table
    this.pawnHash = new Map();
    this.pawnHashSize = 0;
    this.MAX_PAWN_HASH_SIZE = 1000;
  }

  /**
   * Initialize evaluation masks
   */
  initMasks() {
    // File masks (already in engine)
    this.ADJACENT_FILES = new Array(8).fill(0n);
    
    for (let file = 0; file < 8; file++) {
      let mask = 0n;
      if (file > 0) mask |= this.engine.fileMasks[file - 1];
      if (file < 7) mask |= this.engine.fileMasks[file + 1];
      this.ADJACENT_FILES[file] = mask;
    }
  }

  /**
   * Evaluate pawn structure for both sides
   * @param {number} phaseFactor - 0 (middlegame) to 1 (endgame)
   * @returns {number} evaluation score in centipawns
   */
  evaluate(phaseFactor) {
    const hashKey = this.calculatePawnHash();
    
    // Try pawn hash table first
    if (this.pawnHash.has(hashKey)) {
      const entry = this.pawnHash.get(hashKey);
      if (entry.phaseFactor === phaseFactor) {
        return entry.score;
      }
    }
    
    let score = 0;
    
    // Evaluate white pawns
    const whitePawns = this.engine.bitboards[this.engine.COLORS.WHITE * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    score += this.evaluatePawns(whitePawns, this.engine.COLORS.WHITE, phaseFactor);
    
    // Evaluate black pawns
    const blackPawns = this.engine.bitboards[this.engine.COLORS.BLACK * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    score -= this.evaluatePawns(blackPawns, this.engine.COLORS.BLACK, phaseFactor);
    
    // Store in hash table
    if (this.pawnHashSize < this.MAX_PAWN_HASH_SIZE) {
      this.pawnHash.set(hashKey, { score, phaseFactor });
      this.pawnHashSize++;
    }
    
    return score;
  }

  /**
   * Evaluate pawn structure for one color
   * @param {bigint} pawns 
   * @param {number} color 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluatePawns(pawns, color, phaseFactor) {
    if (pawns === 0n) return 0;
    
    let score = 0;
    let pawnBB = pawns;
    
    // Detect pawn features
    const features = this.detectPawnFeatures(pawns, color);
    
    // Evaluate features
    score += this.evaluateDoubledPawns(features.doubledPawns, phaseFactor);
    score += this.evaluateIsolatedPawns(features.isolatedPawns, phaseFactor);
    score += this.evaluateBackwardPawns(features.backwardPawns, phaseFactor);
    score += this.evaluatePassedPawns(features.passedPawns, color, phaseFactor);
    score += this.evaluateConnectedPawns(features.connectedPawns, phaseFactor);
    score += this.evaluatePhalanxPawns(features.phalanxPawns, phaseFactor);
    
    return score;
  }

  /**
   * Detect various pawn structure features
   * @param {bigint} pawns 
   * @param {number} color 
   * @returns {object} detected features
   */
  detectPawnFeatures(pawns, color) {
    const enemyPawns = this.engine.bitboards[(color ^ 1) * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    const features = {
      doubledPawns: 0n,
      isolatedPawns: 0n,
      backwardPawns: 0n,
      passedPawns: 0n,
      connectedPawns: 0n,
      phalanxPawns: 0n
    };
    
    let pawnBB = pawns;
    while (pawnBB) {
      const sq = this.engine.bitScanForward(pawnBB);
      pawnBB &= pawnBB - 1n;
      const file = sq % 8;
      const rank = Math.floor(sq / 8);
      
      // Doubled pawns
      const filePawns = pawns & this.engine.fileMasks[file];
      if (this.engine.popCount(filePawns) > 1) {
        features.doubledPawns |= filePawns;
      }
      
      // Isolated pawns
      if ((pawns & this.ADJACENT_FILES[file]) === 0n) {
        features.isolatedPawns |= 1n << BigInt(sq);
      }
      
      // Passed pawns
      const passedMask = color === this.engine.COLORS.WHITE 
        ? this.engine.passedPawnMasks[this.engine.COLORS.BLACK][sq]
        : this.engine.passedPawnMasks[this.engine.COLORS.WHITE][sq];
      
      if ((enemyPawns & passedMask) === 0n) {
        features.passedPawns |= 1n << BigInt(sq);
      }
      
      // Connected pawns
      const supportingPawns = this.getSupportingPawns(sq, pawns, color);
      if (supportingPawns !== 0n) {
        features.connectedPawns |= 1n << BigInt(sq);
      }
      
      // Phalanx pawns (adjacent on same rank)
      if (file > 0) {
        const leftSq = sq - 1;
        if (pawns & (1n << BigInt(leftSq))) {
          features.phalanxPawns |= 1n << BigInt(sq);
        }
      }
      
      // Backward pawns
      if (this.isBackwardPawn(sq, pawns, enemyPawns, color)) {
        features.backwardPawns |= 1n << BigInt(sq);
      }
    }
    
    return features;
  }

  /**
   * Get pawns that support the given pawn
   * @param {number} sq 
   * @param {bigint} pawns 
   * @param {number} color 
   * @returns {bigint} 
   */
  getSupportingPawns(sq, pawns, color) {
    const file = sq % 8;
    let supporters = 0n;
    
    if (file > 0) {
      const supportingSq = color === this.engine.COLORS.WHITE ? sq + 7 : sq - 9;
      supporters |= pawns & (1n << BigInt(supportingSq));
    }
    
    if (file < 7) {
      const supportingSq = color === this.engine.COLORS.WHITE ? sq + 9 : sq - 7;
      supporters |= pawns & (1n << BigInt(supportingSq));
    }
    
    return supporters;
  }

  /**
   * Check if a pawn is backward
   * @param {number} sq 
   * @param {bigint} pawns 
   * @param {bigint} enemyPawns 
   * @param {number} color 
   * @returns {boolean} 
   */
  isBackwardPawn(sq, pawns, enemyPawns, color) {
    const file = sq % 8;
    const rank = Math.floor(sq / 8);
    
    // Pawns can't be backward on first/last rank
    if ((color === this.engine.COLORS.WHITE && rank === 0) || 
        (color === this.engine.COLORS.BLACK && rank === 7)) {
      return false;
    }
    
    // Check if there are no friendly pawns behind
    const behindMask = color === this.engine.COLORS.WHITE 
      ? this.engine.fileMasks[file] & ~((1n << BigInt(sq)) - 1n)
      : this.engine.fileMasks[file] & ((1n << BigInt(sq)) - 1n);
    
    if ((pawns & behindMask) !== 0n) {
      return false;
    }
    
    // Check if enemy has pawns that can attack this square
    const attackMask = color === this.engine.COLORS.WHITE 
      ? this.engine.pawnAttacks[this.engine.COLORS.BLACK][sq]
      : this.engine.pawnAttacks[this.engine.COLORS.WHITE][sq];
    
    return (enemyPawns & attackMask) !== 0n;
  }

  /**
   * Evaluate doubled pawns penalty
   * @param {bigint} doubledPawns 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateDoubledPawns(doubledPawns, phaseFactor) {
    const count = this.engine.popCount(doubledPawns);
    if (count === 0) return 0;
    
    const penalty = this.DOUBLED_PENALTY[0] * (1 - phaseFactor) + 
                   this.DOUBLED_PENALTY[1] * phaseFactor;
    
    return count * penalty;
  }

  /**
   * Evaluate isolated pawns penalty
   * @param {bigint} isolatedPawns 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateIsolatedPawns(isolatedPawns, phaseFactor) {
    const count = this.engine.popCount(isolatedPawns);
    if (count === 0) return 0;
    
    const penalty = this.ISOLATED_PENALTY[0] * (1 - phaseFactor) + 
                   this.ISOLATED_PENALTY[1] * phaseFactor;
    
    return count * penalty;
  }

  /**
   * Evaluate backward pawns penalty
   * @param {bigint} backwardPawns 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateBackwardPawns(backwardPawns, phaseFactor) {
    const count = this.engine.popCount(backwardPawns);
    if (count === 0) return 0;
    
    const penalty = this.BACKWARD_PENALTY[0] * (1 - phaseFactor) + 
                   this.BACKWARD_PENALTY[1] * phaseFactor;
    
    return count * penalty;
  }

  /**
   * Evaluate passed pawns bonus
   * @param {bigint} passedPawns 
   * @param {number} color 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluatePassedPawns(passedPawns, color, phaseFactor) {
    let score = 0;
    let bb = passedPawns;
    
    while (bb) {
      const sq = this.engine.bitScanForward(bb);
      bb &= bb - 1n;
      
      const rank = Math.floor(sq / 8);
      const advancement = color === this.engine.COLORS.WHITE ? rank : 7 - rank;
      
      let bonus = this.PASSED_BONUS[0] * (1 - phaseFactor) + 
                 this.PASSED_BONUS[1] * phaseFactor;
      
      // Bonus increases with advancement
      bonus += advancement * (10 + phaseFactor * 20);
      
      score += bonus;
    }
    
    return score;
  }

  /**
   * Evaluate connected pawns bonus
   * @param {bigint} connectedPawns 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateConnectedPawns(connectedPawns, phaseFactor) {
    const count = this.engine.popCount(connectedPawns);
    if (count === 0) return 0;
    
    const bonus = this.CONNECTED_BONUS[0] * (1 - phaseFactor) + 
                 this.CONNECTED_BONUS[1] * phaseFactor;
    
    return count * bonus;
  }

  /**
   * Evaluate phalanx pawns bonus
   * @param {bigint} phalanxPawns 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluatePhalanxPawns(phalanxPawns, phaseFactor) {
    const count = this.engine.popCount(phalanxPawns);
    if (count === 0) return 0;
    
    const bonus = this.PHALANX_BONUS[0] * (1 - phaseFactor) + 
                 this.PHALANX_BONUS[1] * phaseFactor;
    
    return count * bonus;
  }

  /**
   * Calculate pawn structure hash key
   * @returns {bigint} 
   */
  calculatePawnHash() {
    let hash = 0n;
    const whitePawns = this.engine.bitboards[this.engine.COLORS.WHITE * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    const blackPawns = this.engine.bitboards[this.engine.COLORS.BLACK * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    
    // Hash pawn positions
    hash ^= this.engine.hashPawns(whitePawns, this.engine.COLORS.WHITE);
    hash ^= this.engine.hashPawns(blackPawns, this.engine.COLORS.BLACK);
    
    return hash;
  }

  /**
   * Clear pawn hash table
   */
  clearPawnHash() {
    this.pawnHash.clear();
    this.pawnHashSize = 0;
  }
}

export default PawnStructureEvaluator;
///////////////////////////////////
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

////////////////////////////////////
// evaluation/Mobility.js

class MobilityEvaluator {
  constructor(engine) {
    this.engine = engine;
    
    // Mobility bonuses by piece type [middlegame, endgame]
    this.MOBILITY_BONUS = {
      [this.engine.PIECE_TYPES.KNIGHT]: [12, 8],
      [this.engine.PIECE_TYPES.BISHOP]: [8, 12],
      [this.engine.PIECE_TYPES.ROOK]: [6, 10],
      [this.engine.PIECE_TYPES.QUEEN]: [4, 6],
      
      // Piece weights for mobility calculation
      WEIGHTS: [1.0, 0.8, 0.6, 0.4]
    };
    
    // Outpost bonuses [knight, bishop]
    this.OUTPOST_BONUS = [25, 15];
    
    // Initialize attack tables
    this.initAttackTables();
  }

  /**
   * Initialize attack tables for mobility calculation
   */
  initAttackTables() {
    // Uses engine's existing attack tables
  }

  /**
   * Evaluate mobility for both sides
   * @param {number} phaseFactor - 0 (middlegame) to 1 (endgame)
   * @returns {number} mobility score in centipawns
   */
  evaluate(phaseFactor) {
    let score = 0;
    
    // Evaluate white mobility
    score += this.evaluateColorMobility(this.engine.COLORS.WHITE, phaseFactor);
    
    // Evaluate black mobility
    score -= this.evaluateColorMobility(this.engine.COLORS.BLACK, phaseFactor);
    
    return score;
  }

  /**
   * Evaluate mobility for one color
   * @param {number} color 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateColorMobility(color, phaseFactor) {
    let score = 0;
    const them = color ^ 1;
    const friendlyPieces = this.engine.occupancy[color];
    const enemyPieces = this.engine.occupancy[them];
    const allPieces = this.engine.occupancy[2];
    
    // Knight mobility
    score += this.evaluatePieceMobility(
      this.engine.PIECE_TYPES.KNIGHT,
      color,
      friendlyPieces,
      allPieces,
      phaseFactor
    );
    
    // Bishop mobility
    score += this.evaluatePieceMobility(
      this.engine.PIECE_TYPES.BISHOP,
      color,
      friendlyPieces,
      allPieces,
      phaseFactor
    );
    
    // Rook mobility
    score += this.evaluatePieceMobility(
      this.engine.PIECE_TYPES.ROOK,
      color,
      friendlyPieces,
      allPieces,
      phaseFactor
    );
    
    // Queen mobility
    score += this.evaluatePieceMobility(
      this.engine.PIECE_TYPES.QUEEN,
      color,
      friendlyPieces,
      allPieces,
      phaseFactor
    );
    
    // Evaluate outposts
    score += this.evaluateOutposts(color, phaseFactor);
    
    return score;
  }

  /**
   * Evaluate mobility for a specific piece type
   * @param {number} pieceType 
   * @param {number} color 
   * @param {bigint} friendlyPieces 
   * @param {bigint} allPieces 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluatePieceMobility(pieceType, color, friendlyPieces, allPieces, phaseFactor) {
    let score = 0;
    const pieces = this.engine.bitboards[color * 6 + pieceType - 1];
    let pieceBB = pieces;
    
    while (pieceBB) {
      const sq = this.engine.bitScanForward(pieceBB);
      pieceBB &= pieceBB - 1n;
      
      // Get attack squares
      let attacks;
      switch (pieceType) {
        case this.engine.PIECE_TYPES.KNIGHT:
          attacks = this.engine.knightAttacks[sq];
          break;
        case this.engine.PIECE_TYPES.BISHOP:
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq);
          break;
        case this.engine.PIECE_TYPES.ROOK:
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq);
          break;
        case this.engine.PIECE_TYPES.QUEEN:
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.QUEEN, sq);
          break;
        default:
          attacks = 0n;
      }
      
      // Remove friendly pieces from attack squares
      attacks &= ~friendlyPieces;
      
      // Count mobility squares
      const mobility = this.engine.popCount(attacks);
      
      // Apply bonus based on piece type and phase
      const bonus = this.MOBILITY_BONUS[pieceType][0] * (1 - phaseFactor) +
                   this.MOBILITY_BONUS[pieceType][1] * phaseFactor;
      
      score += mobility * bonus;
      
      // Additional bonus for attacking squares near enemy king
      if (pieceType !== this.engine.PIECE_TYPES.KING) {
        score += this.evaluateKingAttack(sq, attacks, color, pieceType, phaseFactor);
      }
    }
    
    return score;
  }

  /**
   * Evaluate outpost squares for knights and bishops
   * @param {number} color 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateOutposts(color, phaseFactor) {
    let score = 0;
    const them = color ^ 1;
    const enemyPawns = this.engine.bitboards[them * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    const friendlyPawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    
    // Knight outposts
    const knights = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.KNIGHT - 1];
    let knightBB = knights;
    
    while (knightBB) {
      const sq = this.engine.bitScanForward(knightBB);
      knightBB &= knightBB - 1n;
      
      if (this.isOutpost(sq, color, enemyPawns, friendlyPawns)) {
        score += this.OUTPOST_BONUS[0] * (1 - phaseFactor * 0.5);
      }
    }
    
    // Bishop outposts
    const bishops = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.BISHOP - 1];
    let bishopBB = bishops;
    
    while (bishopBB) {
      const sq = this.engine.bitScanForward(bishopBB);
      bishopBB &= bishopBB - 1n;
      
      if (this.isOutpost(sq, color, enemyPawns, friendlyPawns)) {
        score += this.OUTPOST_BONUS[1] * (1 - phaseFactor * 0.5);
      }
    }
    
    return score;
  }

  /**
   * Check if square is an outpost for the given color
   * @param {number} sq 
   * @param {number} color 
   * @param {bigint} enemyPawns 
   * @param {bigint} friendlyPawns 
   * @returns {boolean} 
   */
  isOutpost(sq, color, enemyPawns, friendlyPawns) {
    const rank = Math.floor(sq / 8);
    const file = sq % 8;
    
    // Outposts must be in enemy territory
    if ((color === this.engine.COLORS.WHITE && rank < 4) ||
        (color === this.engine.COLORS.BLACK && rank > 3)) {
      return false;
    }
    
    // Square must not be attackable by enemy pawns
    const attackedByEnemyPawns = color === this.engine.COLORS.WHITE
      ? ((enemyPawns & this.engine.pawnAttacks[this.engine.COLORS.BLACK][sq]) !== 0n)
      : ((enemyPawns & this.engine.pawnAttacks[this.engine.COLORS.WHITE][sq]) !== 0n);
    
    if (attackedByEnemyPawns) {
      return false;
    }
    
    // Should be protected by friendly pawn
    const protectedByFriendlyPawn = color === this.engine.COLORS.WHITE
      ? ((friendlyPawns & this.engine.pawnAttacks[this.engine.COLORS.WHITE][sq]) !== 0n)
      : ((friendlyPawns & this.engine.pawnAttacks[this.engine.COLORS.BLACK][sq]) !== 0n);
    
    return protectedByFriendlyPawn;
  }

  /**
   * Evaluate king attack bonuses
   * @param {number} sq 
   * @param {bigint} attacks 
   * @param {number} color 
   * @param {number} pieceType 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  evaluateKingAttack(sq, attacks, color, pieceType, phaseFactor) {
    const them = color ^ 1;
    const enemyKingSq = this.engine.bitScanForward(
      this.engine.bitboards[them * 6 + this.engine.PIECE_TYPES.KING - 1]
    );
    
    if (enemyKingSq === -1) return 0;
    
    // Get king safety mask
    const kingSafetyMask = this.engine.kingSafetyMask[enemyKingSq];
    
    // Count attacks on king safety zone
    const kingAttacks = this.engine.popCount(attacks & kingSafetyMask);
    
    if (kingAttacks === 0) return 0;
    
    // Weight based on piece type
    const weight = this.MOBILITY_BONUS.WEIGHTS[pieceType - 2]; // Knight=0, Bishop=1, etc.
    
    // Bonus increases in middlegame
    const bonus = kingAttacks * weight * 10 * (1 - phaseFactor * 0.7);
    
    return bonus;
  }

  /**
   * Get mobility score for a specific piece on a square
   * @param {number} pieceType 
   * @param {number} sq 
   * @param {number} color 
   * @param {number} phaseFactor 
   * @returns {number} 
   */
  getPieceMobility(pieceType, sq, color, phaseFactor) {
    const friendlyPieces = this.engine.occupancy[color];
    let attacks;
    
    switch (pieceType) {
      case this.engine.PIECE_TYPES.KNIGHT:
        attacks = this.engine.knightAttacks[sq];
        break;
      case this.engine.PIECE_TYPES.BISHOP:
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq);
        break;
      case this.engine.PIECE_TYPES.ROOK:
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq);
        break;
      case this.engine.PIECE_TYPES.QUEEN:
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.QUEEN, sq);
        break;
      default:
        return 0;
    }
    
    attacks &= ~friendlyPieces;
    const mobility = this.engine.popCount(attacks);
    
    const bonus = this.MOBILITY_BONUS[pieceType][0] * (1 - phaseFactor) +
                 this.MOBILITY_BONUS[pieceType][1] * phaseFactor;
    
    return mobility * bonus;
  }
}

export default MobilityEvaluator;
////////////////////////////////
// ================ KING SAFETY EVALUATION MODULE =====================
class KingSafetyEvaluator {
  constructor(engine) {
    this.engine = engine;
    
    // Safety scores based on number of attackers
    this.SAFETY_TABLE = [
      0,    // 0 attackers
      0,    // 1 attacker
      10,   // 2 attackers
      30,   // 3 attackers
      60,   // 4 attackers
      100,  // 5 attackers
      150,  // 6 attackers
      220   // 7+ attackers
    ];
    
    // Penalty for open files near king
    this.OPEN_FILE_PENALTY = [15, 25, 40];
    
    // Penalty for semi-open files near king
    this.SEMI_OPEN_FILE_PENALTY = [10, 15, 25];
    
    // Bonus for pawn shelter in front of king
    this.SHELTER_BONUS = [
      [ 0,  0,  0,  0,  0,  0,  0,  0],
      [ 5, 10, 15, 20, 20, 15, 10,  5],
      [10, 20, 30, 40, 40, 30, 20, 10],
      [15, 30, 45, 60, 60, 45, 30, 15]
    ];
    
    // Storm penalty when enemy pawns can attack shelter squares
    this.STORM_PENALTY = [
      [ 0,   0,   0,   0,   0,   0,   0,   0],
      [10,  15,  20,  25,  25,  20,  15,  10],
      [20,  30,  40,  50,  50,  40,  30,  20],
      [30,  45,  60,  75,  75,  60,  45,  30]
    ];
    
    // King attack weights by piece type
    this.ATTACK_WEIGHTS = {
      [this.engine.PIECE_TYPES.PAWN]: 0,
      [this.engine.PIECE_TYPES.KNIGHT]: 2,
      [this.engine.PIECE_TYPES.BISHOP]: 1,
      [this.engine.PIECE_TYPES.ROOK]: 1,
      [this.engine.PIECE_TYPES.QUEEN]: 3,
      [this.engine.PIECE_TYPES.KING]: 0
    };
    
    // Initialize attack zones
    this.initKingZones();
  }

  initKingZones() {
    // Precompute king safety zones (squares around king)
    this.KING_ZONE = new Array(64).fill(0n);
    
    for (let sq = 0; sq < 64; sq++) {
      const file = sq % 8;
      const rank = Math.floor(sq / 8);
      
      // Include squares within 2 squares of the king
      for (let f = Math.max(0, file - 2); f <= Math.min(7, file + 2); f++) {
        for (let r = Math.max(0, rank - 2); r <= Math.min(7, rank + 2); r++) {
          this.KING_ZONE[sq] |= 1n << BigInt(r * 8 + f);
        }
      }
    }
  }

  evaluate(phaseFactor) {
    // King safety is less important in endgames
    if (phaseFactor > 0.7) return 0;
    
    let score = 0;
    
    // Evaluate white king safety
    score += this.evaluateKingSafety(this.engine.COLORS.WHITE);
    
    // Evaluate black king safety
    score -= this.evaluateKingSafety(this.engine.COLORS.BLACK);
    
    // Scale by game phase (more important in opening/middlegame)
    return Math.round(score * (1 - phaseFactor * 0.7));
  }

  evaluateKingSafety(color) {
    const them = color ^ 1;
    const kingSq = this.engine.bitScanForward(
      this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.KING - 1]
    );
    
    // 1. Pawn shelter and storm evaluation
    let safetyScore = this.evaluatePawnShelter(color, kingSq);
    
    // 2. Open and semi-open files near king
    safetyScore -= this.evaluateOpenFiles(color, kingSq);
    
    // 3. Piece attacks on king zone
    const attackScore = this.evaluateKingAttacks(them, kingSq);
    safetyScore -= this.SAFETY_TABLE[Math.min(7, attackScore)];
    
    // 4. King mobility (restricted mobility is bad)
    safetyScore -= this.evaluateKingMobility(color, kingSq);
    
    // 5. No pawns penalty (if king has no pawns left)
    if ((this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1] & this.KING_ZONE[kingSq]) === 0n) {
      safetyScore -= 30;
    }
    
    return safetyScore;
  }

  evaluatePawnShelter(color, kingSq) {
    const kingFile = kingSq % 8;
    const kingRank = Math.floor(kingSq / 8);
    let shelterScore = 0;
    
    // Check files adjacent to king (including king's file)
    for (let file = Math.max(0, kingFile - 1); file <= Math.min(7, kingFile + 1); file++) {
      // Find closest pawn in front of king
      let foundPawn = false;
      const pawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
      
      if (color === this.engine.COLORS.WHITE) {
        // White king - look for pawns behind (lower ranks)
        for (let rank = kingRank - 1; rank >= 0; rank--) {
          const sq = rank * 8 + file;
          if (pawns & (1n << BigInt(sq))) {
            const distance = kingRank - rank;
            shelterScore += this.SHELTER_BONUS[Math.min(3, distance)][file];
            foundPawn = true;
            break;
          }
        }
      } else {
        // Black king - look for pawns in front (higher ranks)
        for (let rank = kingRank + 1; rank < 8; rank++) {
          const sq = rank * 8 + file;
          if (pawns & (1n << BigInt(sq))) {
            const distance = rank - kingRank;
            shelterScore += this.SHELTER_BONUS[Math.min(3, distance)][file];
            foundPawn = true;
            break;
          }
        }
      }
      
      // Evaluate enemy pawn storms if we have no pawn on this file
      if (!foundPawn) {
        shelterScore -= this.evaluatePawnStorm(color ^ 1, file, kingRank);
      }
    }
    
    return shelterScore;
  }

  evaluatePawnStorm(opponentColor, file, kingRank) {
    const pawns = this.engine.bitboards[opponentColor * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    const fileMask = this.engine.fileMasks[file];
    const filePawns = pawns & fileMask;
    
    if (!filePawns) return 0;
    
    let stormPenalty = 0;
    let closestPawnDist = 8;
    
    // Find closest opponent pawn on this file
    let bb = filePawns;
    while (bb) {
      const sq = this.engine.bitScanForward(bb);
      bb &= bb - 1n;
      const rank = Math.floor(sq / 8);
      
      const distance = opponentColor === this.engine.COLORS.WHITE ? 
        kingRank - rank : 
        rank - kingRank;
      
      if (distance > 0 && distance < closestPawnDist) {
        closestPawnDist = distance;
      }
    }
    
    if (closestPawnDist < 4) {
      stormPenalty = this.STORM_PENALTY[Math.min(3, closestPawnDist)][file];
    }
    
    return stormPenalty;
  }

  evaluateOpenFiles(color, kingSq) {
    const kingFile = kingSq % 8;
    let penalty = 0;
    
    // Check king's file and adjacent files
    for (let file = Math.max(0, kingFile - 1); file <= Math.min(7, kingFile + 1); file++) {
      const fileMask = this.engine.fileMasks[file];
      const ourPawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1] & fileMask;
      const theirPawns = this.engine.bitboards[(color ^ 1) * 6 + this.engine.PIECE_TYPES.PAWN - 1] & fileMask;
      
      if (!ourPawns) {
        // Open file (no friendly pawns)
        penalty += this.OPEN_FILE_PENALTY[Math.abs(file - kingFile)];
      } else if (!theirPawns) {
        // Semi-open file (no enemy pawns)
        penalty += this.SEMI_OPEN_FILE_PENALTY[Math.abs(file - kingFile)];
      }
      
      // Extra penalty if opponent has rook or queen on this file
      const theirRooksQueens = (
        this.engine.bitboards[(color ^ 1) * 6 + this.engine.PIECE_TYPES.ROOK - 1] |
        this.engine.bitboards[(color ^ 1) * 6 + this.engine.PIECE_TYPES.QUEEN - 1]
      ) & fileMask;
      
      if (theirRooksQueens) {
        penalty += 20 * (3 - Math.abs(file - kingFile));
      }
    }
    
    return penalty;
  }

  evaluateKingAttacks(attackerColor, kingSq) {
    let attackScore = 0;
    const zone = this.KING_ZONE[kingSq];
    const occupancy = this.engine.occupancy[2];
    
    // Evaluate each piece type's attacks on king zone
    for (let piece = this.engine.PIECE_TYPES.KNIGHT; piece <= this.engine.PIECE_TYPES.QUEEN; piece++) {
      const pieces = this.engine.bitboards[attackerColor * 6 + piece - 1];
      let bb = pieces;
      
      while (bb) {
        const sq = this.engine.bitScanForward(bb);
        bb &= bb - 1n;
        
        // Get attacks from this square to king zone
        let attacks;
        if (piece === this.engine.PIECE_TYPES.KNIGHT) {
          attacks = this.engine.knightAttacks[sq] & zone;
        } else if (piece === this.engine.PIECE_TYPES.BISHOP) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq) & zone;
        } else if (piece === this.engine.PIECE_TYPES.ROOK) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq) & zone;
        } else if (piece === this.engine.PIECE_TYPES.QUEEN) {
          attacks = (
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq) |
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq)
          ) & zone;
        }
        
        // Count number of attacked squares in king zone
        const attackCount = this.engine.popCount(attacks);
        attackScore += attackCount * this.ATTACK_WEIGHTS[piece];
      }
    }
    
    // Bonus for multiple attackers
    if (attackScore >= 6) {
      attackScore += 2;
    }
    
    return attackScore;
  }

  evaluateKingMobility(color, kingSq) {
    const them = color ^ 1;
    const kingMoves = this.engine.kingAttacks[kingSq];
    const safeMoves = kingMoves & ~this.engine.occupancy[color] & ~this.engine.getAttacks(them);
    
    const mobility = this.engine.popCount(safeMoves);
    const maxMobility = this.engine.popCount(kingMoves & ~this.engine.occupancy[color]);
    
    // Penalty based on percentage of mobility lost
    if (maxMobility > 0) {
      const mobilityLoss = 100 * (maxMobility - mobility) / maxMobility;
      return Math.round(mobilityLoss / 10); // 0-10 penalty
    }
    
    return 0;
  }

  // Helper to get all squares attacked by a color
  getAttacks(color) {
    let attacks = 0n;
    
    // Pawn attacks
    let pawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
    while (pawns) {
      const sq = this.engine.bitScanForward(pawns);
      pawns &= pawns - 1n;
      attacks |= this.engine.pawnAttacks[color][sq];
    }
    
    // Knight attacks
    let knights = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.KNIGHT - 1];
    while (knights) {
      const sq = this.engine.bitScanForward(knights);
      knights &= knights - 1n;
      attacks |= this.engine.knightAttacks[sq];
    }
    
    // Bishop attacks
    let bishops = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.BISHOP - 1];
    while (bishops) {
      const sq = this.engine.bitScanForward(bishops);
      bishops &= bishops - 1n;
      attacks |= this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq);
    }
    
    // Rook attacks
    let rooks = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.ROOK - 1];
    while (rooks) {
      const sq = this.engine.bitScanForward(rooks);
      rooks &= rooks - 1n;
      attacks |= this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq);
    }
    
    // Queen attacks
    let queens = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.QUEEN - 1];
    while (queens) {
      const sq = this.engine.bitScanForward(queens);
      queens &= queens - 1n;
      attacks |= (
        this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq) |
        this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq)
      );
    }
    
    // King attacks
    const kingSq = this.engine.bitScanForward(
      this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.KING - 1]
    );
    attacks |= this.engine.kingAttacks[kingSq];
    
    return attacks;
  }
}

export default KingSafetyEvaluator;
/////////////////////////////////
// ================ THREAT EVALUATION MODULE =====================
class ThreatEvaluator {
  constructor(engine) {
    this.engine = engine;
    
    // Threat bonuses by piece type [attacker][victim]
    this.THREAT_BONUS = [
      /* attacker: none */ [0, 0, 0, 0, 0, 0, 0],
      /* attacker: pawn */ [0, 0, 5, 10, 25, 50, 0],
      /* attacker: knight */ [0, 5, 5, 15, 25, 40, 0],
      /* attacker: bishop */ [0, 5, 15, 15, 25, 40, 0],
      /* attacker: rook */ [0, 10, 15, 20, 30, 40, 0],
      /* attacker: queen */ [0, 10, 20, 30, 40, 50, 0],
      /* attacker: king */ [0, 0, 0, 0, 0, 0, 0]
    ];
    
    // Hanging piece penalty
    this.HANGING_PENALTY = [0, 50, 75, 88, 94, 97, 99];
    
    // Weak square penalty (based on number of attackers/defenders)
    this.WEAK_SQUARE_PENALTY = [0, 10, 25, 50, 75, 100, 125];
    
    // Safe check bonus (checks that can't be captured)
    this.SAFE_CHECK_BONUS = [0, 10, 20, 30, 40, 50];
    
    // Initialize attack tables
    this.initAttackTables();
  }

  initAttackTables() {
    // Precompute squares between any two squares for discovered attacks
    this.BETWEEN_SQS = Array.from({length: 64}, () => 
      Array.from({length: 64}, () => 0n)
    );
    
    for (let from = 0; from < 64; from++) {
      for (let to = 0; to < 64; to++) {
        if (from === to) continue;
        
        const dx = Math.sign((to % 8) - (from % 8));
        const dy = Math.sign(Math.floor(to / 8) - Math.floor(from / 8));
        
        if (dx === 0 || dy === 0 || Math.abs(dx) === Math.abs(dy)) {
          let between = 0n;
          let sq = from + dy * 8 + dx;
          
          while (sq !== to && sq >= 0 && sq < 64) {
            between |= 1n << BigInt(sq);
            sq += dy * 8 + dx;
          }
          
          this.BETWEEN_SQS[from][to] = between;
        }
      }
    }
  }

  evaluate() {
    let score = 0;
    
    // Evaluate threats for white
    score += this.evaluateThreats(this.engine.COLORS.WHITE, this.engine.COLORS.BLACK);
    
    // Evaluate threats for black
    score -= this.evaluateThreats(this.engine.COLORS.BLACK, this.engine.COLORS.WHITE);
    
    return score;
  }

  evaluateThreats(attackerColor, victimColor) {
    let threatScore = 0;
    const victimOccupancy = this.engine.occupancy[victimColor];
    
    // 1. Evaluate piece threats
    threatScore += this.evaluatePieceThreats(attackerColor, victimColor);
    
    // 2. Evaluate hanging pieces
    threatScore += this.evaluateHangingPieces(attackerColor, victimColor);
    
    // 3. Evaluate weak squares
    threatScore += this.evaluateWeakSquares(attackerColor, victimColor);
    
    // 4. Evaluate safe checks
    threatScore += this.evaluateSafeChecks(attackerColor, victimColor);
    
    return threatScore;
  }

  evaluatePieceThreats(attackerColor, victimColor) {
    let threatScore = 0;
    const victimOccupancy = this.engine.occupancy[victimColor];
    
    // Check threats from each attacker piece type
    for (let attackerType = this.engine.PIECE_TYPES.PAWN; 
         attackerType <= this.engine.PIECE_TYPES.QUEEN; 
         attackerType++) {
      
      let attackers = this.engine.bitboards[attackerColor * 6 + attackerType - 1];
      
      while (attackers) {
        const from = this.engine.bitScanForward(attackers);
        attackers &= attackers - 1n;
        
        // Get attacks from this square
        let attacks;
        if (attackerType === this.engine.PIECE_TYPES.PAWN) {
          attacks = this.engine.pawnAttacks[attackerColor][from] & victimOccupancy;
        } else if (attackerType === this.engine.PIECE_TYPES.KNIGHT) {
          attacks = this.engine.knightAttacks[from] & victimOccupancy;
        } else if (attackerType === this.engine.PIECE_TYPES.BISHOP) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, from) & victimOccupancy;
        } else if (attackerType === this.engine.PIECE_TYPES.ROOK) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, from) & victimOccupancy;
        } else if (attackerType === this.engine.PIECE_TYPES.QUEEN) {
          attacks = (
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, from) |
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, from)
          ) & victimOccupancy;
        }
        
        // Evaluate each threatened piece
        while (attacks) {
          const to = this.engine.bitScanForward(attacks);
          attacks &= attacks - 1n;
          
          // Find victim piece type
          const victimType = this.getPieceAt(to, victimColor);
          
          // Add threat bonus based on attacker/victim types
          threatScore += this.THREAT_BONUS[attackerType][victimType];
          
          // Bonus for threatening undefended pieces
          if (!this.isDefended(to, victimColor)) {
            threatScore += this.THREAT_BONUS[attackerType][victimType] / 2;
          }
          
          // Bonus for threats to squares near enemy king
          const enemyKingSq = this.engine.bitScanForward(
            this.engine.bitboards[victimColor * 6 + this.engine.PIECE_TYPES.KING - 1]
          );
          
          if (this.engine.kingAttacks[enemyKingSq] & (1n << BigInt(to))) {
            threatScore += 10;
          }
        }
      }
    }
    
    return threatScore;
  }

  evaluateHangingPieces(attackerColor, victimColor) {
    let penalty = 0;
    const victimPieces = this.engine.occupancy[victimColor];
    
    // Check each victim piece
    let pieces = victimPieces;
    while (pieces) {
      const sq = this.engine.bitScanForward(pieces);
      pieces &= pieces - 1n;
      
      const pieceType = this.getPieceAt(sq, victimColor);
      
      // Skip kings
      if (pieceType === this.engine.PIECE_TYPES.KING) continue;
      
      // Count attackers and defenders
      const attackers = this.countAttackers(attackerColor, sq);
      const defenders = this.countDefenders(victimColor, sq);
      
      // If more attackers than defenders, piece is hanging
      if (attackers > defenders) {
        const dangerLevel = Math.min(6, attackers - defenders);
        penalty += this.HANGING_PENALTY[dangerLevel] * this.engine.PIECE_VALUES[pieceType][0] / 100;
      }
    }
    
    return penalty;
  }

  evaluateWeakSquares(attackerColor, victimColor) {
    let penalty = 0;
    const victimKingSq = this.engine.bitScanForward(
      this.engine.bitboards[victimColor * 6 + this.engine.PIECE_TYPES.KING - 1]
    );
    
    // Evaluate squares in enemy territory (first 4 ranks for white, last 4 for black)
    const territoryMask = victimColor === this.engine.COLORS.WHITE ? 
      0xFFFFFFFF00000000n : 0x00000000FFFFFFFFn;
    
    let squares = this.engine.occupancy[2] & territoryMask;
    while (squares) {
      const sq = this.engine.bitScanForward(squares);
      squares &= squares - 1n;
      
      // Skip squares next to enemy king (handled by king safety)
      if (this.engine.kingAttacks[victimKingSq] & (1n << BigInt(sq))) {
        continue;
      }
      
      // Count attackers and defenders
      const attackers = this.countAttackers(attackerColor, sq);
      const defenders = this.countDefenders(victimColor, sq);
      
      // If more attackers than defenders, square is weak
      if (attackers > defenders) {
        const weakness = Math.min(6, attackers - defenders);
        penalty += this.WEAK_SQUARE_PENALTY[weakness];
      }
    }
    
    return penalty;
  }

  evaluateSafeChecks(attackerColor, victimColor) {
    let bonus = 0;
    const victimKingSq = this.engine.bitScanForward(
      this.engine.bitboards[victimColor * 6 + this.engine.PIECE_TYPES.KING - 1]
    );
    
    // Check for safe checks from each piece type
    for (let pieceType = this.engine.PIECE_TYPES.KNIGHT; 
         pieceType <= this.engine.PIECE_TYPES.QUEEN; 
         pieceType++) {
      
      let pieces = this.engine.bitboards[attackerColor * 6 + pieceType - 1];
      
      while (pieces) {
        const from = this.engine.bitScanForward(pieces);
        pieces &= pieces - 1n;
        
        // Get attacks to king square
        let attacks;
        if (pieceType === this.engine.PIECE_TYPES.KNIGHT) {
          attacks = this.engine.knightAttacks[from] & (1n << BigInt(victimKingSq));
        } else if (pieceType === this.engine.PIECE_TYPES.BISHOP) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, from) & (1n << BigInt(victimKingSq));
        } else if (pieceType === this.engine.PIECE_TYPES.ROOK) {
          attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, from) & (1n << BigInt(victimKingSq));
        } else if (pieceType === this.engine.PIECE_TYPES.QUEEN) {
          attacks = (
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, from) |
            this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, from)
          ) & (1n << BigInt(victimKingSq));
        }
        
        if (attacks) {
          // Check if the check is safe (can't be captured)
          if (!this.isAttacked(from, victimColor)) {
            const safeLevel = Math.min(5, this.engine.PIECE_VALUES[pieceType][0] / 50);
            bonus += this.SAFE_CHECK_BONUS[safeLevel];
          }
        }
      }
    }
    
    return bonus;
  }

  // Helper methods
  countAttackers(attackerColor, sq) {
    let count = 0;
    
    // Pawn attacks
    if (this.engine.pawnAttacks[attackerColor ^ 1][sq] & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.PAWN - 1]) {
      count++;
    }
    
    // Knight attacks
    if (this.engine.knightAttacks[sq] & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.KNIGHT - 1]) {
      count++;
    }
    
    // Bishop attacks
    if (this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sq) & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.BISHOP - 1]) {
      count++;
    }
    
    // Rook attacks
    if (this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sq) & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.ROOK - 1]) {
      count++;
    }
    
    // Queen attacks
    if (this.engine.getSliderAttacks(this.engine.PIECE_TYPES.QUEEN, sq) & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.QUEEN - 1]) {
      count++;
    }
    
    // King attacks
    if (this.engine.kingAttacks[sq] & 
        this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.KING - 1]) {
      count++;
    }
    
    return count;
  }

  countDefenders(defenderColor, sq) {
    return this.countAttackers(defenderColor, sq);
  }

  isAttacked(sq, byColor) {
    return this.countAttackers(byColor, sq) > 0;
  }

  isDefended(sq, byColor) {
    return this.countDefenders(byColor, sq) > 0;
  }

  getPieceAt(sq, color) {
    for (let type = 1; type <= 6; type++) {
      if (this.engine.bitboards[color * 6 + type - 1] & (1n << BigInt(sq))) {
        return type;
      }
    }
    return 0;
  }

  // Method to detect discovered attacks
  hasDiscoveredAttack(attackerColor, from, to) {
    // Get all pieces that could reveal an attack by moving
    const slidingPieces = this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.BISHOP - 1] |
                         this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.ROOK - 1] |
                         this.engine.bitboards[attackerColor * 6 + this.engine.PIECE_TYPES.QUEEN - 1];
    
    // Check if moving the piece reveals an attack
    const between = this.BETWEEN_SQS[from][to];
    if (!between) return false;
    
    // Look for sliding pieces that are aligned with this move
    const alignedSliders = slidingPieces & between;
    if (!alignedSliders) return false;
    
    // Check if any slider now has a line to enemy pieces
    let sliders = alignedSliders;
    while (sliders) {
      const sliderSq = this.engine.bitScanForward(sliders);
      sliders &= sliders - 1n;
      
      const pieceType = this.getPieceAt(sliderSq, attackerColor);
      let attacks;
      
      if (pieceType === this.engine.PIECE_TYPES.BISHOP) {
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.BISHOP, sliderSq);
      } else if (pieceType === this.engine.PIECE_TYPES.ROOK) {
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.ROOK, sliderSq);
      } else if (pieceType === this.engine.PIECE_TYPES.QUEEN) {
        attacks = this.engine.getSliderAttacks(this.engine.PIECE_TYPES.QUEEN, sliderSq);
      }
      
      // Check if attacks reach enemy pieces
      if (attacks & this.engine.occupancy[attackerColor ^ 1]) {
        return true;
      }
    }
    
    return false;
  }
}

export default ThreatEvaluator;
///////////////////////////////////
// ================ UCI PROTOCOL HANDLER =====================
class UCIHandler {
  constructor(engine) {
    this.engine = engine;
    this.isReady = false;
    this.searching = false;
    this.currentSearch = null;
    
    // Bind methods
    this.handleCommand = this.handleCommand.bind(this);
    this.send = this.send.bind(this);
    
    // Initialize communication
    process.stdin.setEncoding('utf8');
    process.stdin.on('data', this.handleCommand);
    
    // Register engine
    this.send('id name SKY5L Chess Engine');
    this.send('id author Your Name');
    this.send('uciok');
  }

  handleCommand(data) {
    const commands = data.trim().split('\n');
    
    for (const cmd of commands) {
      if (!cmd) continue;
      
      const parts = cmd.trim().split(/\s+/);
      const command = parts[0];
      const args = parts.slice(1);
      
      switch (command) {
        case 'uci':
          this.send('id name SKY5L Chess Engine');
          this.send('id author Your Name');
          this.send('uciok');
          break;
          
        case 'isready':
          if (this.isReady) {
            this.send('readyok');
          } else {
            this.engine.init().then(() => {
              this.isReady = true;
              this.send('readyok');
            });
          }
          break;
          
        case 'position':
          this.handlePosition(args);
          break;
          
        case 'go':
          this.handleGo(args);
          break;
          
        case 'stop':
          this.handleStop();
          break;
          
        case 'quit':
          this.handleQuit();
          break;
          
        case 'ucinewgame':
          this.handleNewGame();
          break;
          
        case 'setoption':
          this.handleSetOption(args);
          break;
          
        case 'debug':
          this.handleDebug(args);
          break;
          
        case 'ponderhit':
          this.handlePonderHit();
          break;
          
        default:
          this.send(`info string Unknown command: ${command}`);
          break;
      }
    }
  }

  handlePosition(args) {
    let movesIndex = args.indexOf('moves');
    let fen = args[0] === 'startpos' ? 
      'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1' : 
      args.slice(1, movesIndex !== -1 ? movesIndex : undefined).join(' ');
    
    this.engine.setPosition(fen);
    
    if (movesIndex !== -1) {
      const moves = args.slice(movesIndex + 1);
      for (const move of moves) {
        this.engine.makeMove(this.parseUCIMove(move));
      }
    }
  }

  handleGo(args) {
    if (this.searching) return;
    
    const options = this.parseGoOptions(args);
    this.searching = true;
    
    this.currentSearch = this.engine.getBestMove(options).then(bestMove => {
      if (!this.searching) return;
      
      if (bestMove) {
        this.send(`bestmove ${this.toUCIMove(bestMove)}`);
      } else {
        this.send('bestmove 0000'); // Null move if no legal moves
      }
      
      this.searching = false;
    }).catch(err => {
      this.send(`info string Error in search: ${err}`);
      this.searching = false;
    });
  }

  parseGoOptions(args) {
    const options = {};
    let i = 0;
    
    while (i < args.length) {
      const param = args[i++];
      
      switch (param) {
        case 'wtime':
          options.wtime = parseInt(args[i++]);
          break;
        case 'btime':
          options.btime = parseInt(args[i++]);
          break;
        case 'winc':
          options.winc = parseInt(args[i++]);
          break;
        case 'binc':
          options.binc = parseInt(args[i++]);
          break;
        case 'movestogo':
          options.movestogo = parseInt(args[i++]);
          break;
        case 'depth':
          options.depth = parseInt(args[i++]);
          break;
        case 'nodes':
          options.nodes = parseInt(args[i++]);
          break;
        case 'mate':
          options.mate = parseInt(args[i++]);
          break;
        case 'movetime':
          options.movetime = parseInt(args[i++]);
          break;
        case 'infinite':
          options.infinite = true;
          break;
        case 'ponder':
          options.ponder = true;
          break;
      }
    }
    
    return options;
  }

  handleStop() {
    if (this.searching) {
      this.engine.stopSearch();
      this.searching = false;
    }
  }

  handleQuit() {
    this.handleStop();
    process.exit(0);
  }

  handleNewGame() {
    this.engine.clear();
    this.isReady = false;
  }

  handleSetOption(args) {
    const nameIndex = args.indexOf('name');
    const valueIndex = args.indexOf('value');
    
    if (nameIndex === -1) return;
    
    const name = args.slice(nameIndex + 1, valueIndex !== -1 ? valueIndex : undefined).join(' ');
    const value = valueIndex !== -1 ? args.slice(valueIndex + 1).join(' ') : null;
    
    this.engine.setOption(name, value);
  }

  handleDebug(args) {
    const mode = args[0];
    this.engine.debugMode = mode === 'on';
  }

  handlePonderHit() {
    // Implement ponderhit logic if pondering is supported
  }

  // Utility methods
  parseUCIMove(uciMove) {
    if (uciMove === '0000') return null; // Null move
    
    const from = this.squareToIndex(uciMove.substr(0, 2));
    const to = this.squareToIndex(uciMove.substr(2, 2));
    const promotion = uciMove.length > 4 ? 
      this.pieceFromChar(uciMove[4]) : 0;
    
    const moves = this.engine.generateMoves();
    for (const move of moves) {
      if (move.from === from && move.to === to && 
          (!promotion || move.promotion === promotion)) {
        return move;
      }
    }
    
    return null;
  }

  toUCIMove(move) {
    if (!move) return '0000';
    
    const from = this.indexToSquare(move.from);
    const to = this.indexToSquare(move.to);
    const promo = move.promotion ? this.pieceToChar(move.promotion).toLowerCase() : '';
    
    return from + to + promo;
  }

  squareToIndex(square) {
    const file = square.charCodeAt(0) - 'a'.charCodeAt(0);
    const rank = 8 - parseInt(square[1]);
    return rank * 8 + file;
  }

  indexToSquare(index) {
    const file = String.fromCharCode('a'.charCodeAt(0) + (index % 8));
    const rank = 8 - Math.floor(index / 8);
    return file + rank;
  }

  pieceFromChar(c) {
    switch (c.toLowerCase()) {
      case 'p': return this.engine.PIECE_TYPES.PAWN;
      case 'n': return this.engine.PIECE_TYPES.KNIGHT;
      case 'b': return this.engine.PIECE_TYPES.BISHOP;
      case 'r': return this.engine.PIECE_TYPES.ROOK;
      case 'q': return this.engine.PIECE_TYPES.QUEEN;
      case 'k': return this.engine.PIECE_TYPES.KING;
      default: return 0;
    }
  }

  pieceToChar(piece) {
    switch (piece) {
      case this.engine.PIECE_TYPES.PAWN: return 'P';
      case this.engine.PIECE_TYPES.KNIGHT: return 'N';
      case this.engine.PIECE_TYPES.BISHOP: return 'B';
      case this.engine.PIECE_TYPES.ROOK: return 'R';
      case this.engine.PIECE_TYPES.QUEEN: return 'Q';
      case this.engine.PIECE_TYPES.KING: return 'K';
      default: return '';
    }
  }

  send(message) {
    process.stdout.write(message + '\n');
  }
}

export default UCIHandler;
///////////////////////////////////
// uci/Commands.js
class UCICommands {
    constructor(engine) {
        this.engine = engine;
        this.isReady = false;
        this.searching = false;
        this.currentSearch = null;
    }

    async processCommand(command) {
        const parts = command.trim().split(/\s+/);
        const cmd = parts[0].toLowerCase();

        try {
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
                    return this.handleRegister(parts.slice(1));
                default:
                    return this.sendResponse(`Unknown command: ${cmd}`);
            }
        } catch (error) {
            console.error(`Error processing command ${cmd}:`, error);
            return this.sendResponse(`error ${error.message}`);
        }
    }

    handleUCI() {
        this.sendResponse('id name SKY5L Chess Engine');
        this.sendResponse('id author Your Name');
        
        // Send engine options
        this.sendResponse('option name Hash type spin default 128 min 1 max 65536');
        this.sendResponse('option name Threads type spin default 1 min 1 max 512');
        this.sendResponse('option name Contempt type spin default 0 min -100 max 100');
        this.sendResponse('option name SyzygyPath type string default <empty>');
        
        this.sendResponse('uciok');
    }

    async handleIsReady() {
        if (!this.isReady) {
            await this.engine.init();
            this.isReady = true;
        }
        this.sendResponse('readyok');
    }

    handleUCINewGame() {
        this.engine.reset();
        this.isReady = true;
    }

    handlePosition(args) {
        let fen;
        let moves = [];
        let fenParts = [];
        let moveIndex = args.indexOf('moves');

        if (args[0] === 'startpos') {
            fen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
            if (moveIndex !== -1) {
                moves = args.slice(moveIndex + 1);
            }
        } else if (args[0] === 'fen') {
            if (moveIndex !== -1) {
                fenParts = args.slice(1, moveIndex);
                moves = args.slice(moveIndex + 1);
            } else {
                fenParts = args.slice(1);
            }
            fen = fenParts.join(' ');
        } else {
            throw new Error('Invalid position command');
        }

        // Set the position
        if (fen) {
            this.engine.setPosition(fen);
        }

        // Apply moves
        for (const moveStr of moves) {
            const move = this.engine.parseUCIMove(moveStr);
            if (!move) {
                throw new Error(`Invalid move: ${moveStr}`);
            }
            this.engine.makeMove(move);
        }
    }

    async handleGo(args) {
        if (this.searching) {
            throw new Error('Search already in progress');
        }

        const params = this.parseGoParameters(args);
        this.searching = true;

        try {
            this.currentSearch = this.engine.search(params);
            const bestMove = await this.currentSearch;

            if (this.searching) {
                this.sendResponse(`bestmove ${this.engine.moveToUCI(bestMove)}`);
            }
        } finally {
            this.searching = false;
            this.currentSearch = null;
        }
    }

    parseGoParameters(args) {
        const params = {};
        let i = 0;

        while (i < args.length) {
            const arg = args[i];
            const nextArg = i + 1 < args.length ? args[i + 1] : null;

            switch (arg) {
                case 'wtime':
                    if (nextArg) params.wtime = parseInt(nextArg);
                    i += 2;
                    break;
                case 'btime':
                    if (nextArg) params.btime = parseInt(nextArg);
                    i += 2;
                    break;
                case 'winc':
                    if (nextArg) params.winc = parseInt(nextArg);
                    i += 2;
                    break;
                case 'binc':
                    if (nextArg) params.binc = parseInt(nextArg);
                    i += 2;
                    break;
                case 'movestogo':
                    if (nextArg) params.movestogo = parseInt(nextArg);
                    i += 2;
                    break;
                case 'depth':
                    if (nextArg) params.depth = parseInt(nextArg);
                    i += 2;
                    break;
                case 'nodes':
                    if (nextArg) params.nodes = parseInt(nextArg);
                    i += 2;
                    break;
                case 'mate':
                    if (nextArg) params.mate = parseInt(nextArg);
                    i += 2;
                    break;
                case 'movetime':
                    if (nextArg) params.movetime = parseInt(nextArg);
                    i += 2;
                    break;
                case 'infinite':
                    params.infinite = true;
                    i += 1;
                    break;
                case 'ponder':
                    params.ponder = true;
                    i += 1;
                    break;
                default:
                    i += 1;
            }
        }

        return params;
    }

    async handleStop() {
        if (this.searching && this.currentSearch) {
            this.engine.stopSearch();
            try {
                await this.currentSearch;
            } catch (e) {
                // Search was stopped, ignore errors
            }
            this.searching = false;
            this.currentSearch = null;
        }
    }

    handleQuit() {
        this.handleStop();
        process.exit(0);
    }

    handleDebug(on) {
        this.engine.debugMode = on === 'on';
    }

    handleSetOption(args) {
        const nameIndex = args.indexOf('name');
        const valueIndex = args.indexOf('value');
        
        if (nameIndex === -1) {
            throw new Error('Invalid setoption command');
        }

        const name = valueIndex !== -1 ? 
            args.slice(nameIndex + 1, valueIndex).join(' ') : 
            args.slice(nameIndex + 1).join(' ');
        
        const value = valueIndex !== -1 ? 
            args.slice(valueIndex + 1).join(' ') : 
            null;

        this.setEngineOption(name, value);
    }

    setEngineOption(name, value) {
        switch (name.toLowerCase()) {
            case 'hash':
                const hashSize = parseInt(value);
                if (hashSize >= 1 && hashSize <= 65536) {
                    this.engine.setHashSize(hashSize);
                }
                break;
            case 'threads':
                const threads = parseInt(value);
                if (threads >= 1 && threads <= 512) {
                    this.engine.setThreadCount(threads);
                }
                break;
            case 'contempt':
                const contempt = parseInt(value);
                if (contempt >= -100 && contempt <= 100) {
                    this.engine.setContempt(contempt);
                }
                break;
            case 'syzygypath':
                this.engine.setSyzygyPath(value);
                break;
            default:
                console.log(`Unknown option: ${name}`);
        }
    }

    handlePonderHit() {
        // Implement ponder hit logic if needed
    }

    handleRegister(args) {
        // Implement registration logic if needed
    }

    sendResponse(response) {
        console.log(response);
    }
}

module.exports = UCICommands;
//////////////////////////////////
// utils/Helpers.js
class Helpers {
    static bitScanForward(bb) {
        // Finds the index of the least significant set bit (LSB)
        // Returns -1 if no bits are set
        if (bb === 0n) return -1;
        return BigInt.asUintN(64, bb & -bb).toString(2).length - 1;
    }

    static bitScanReverse(bb) {
        // Finds the index of the most significant set bit (MSB)
        if (bb === 0n) return -1;
        let msb = 0;
        while (bb > 1n) {
            bb >>= 1n;
            msb++;
        }
        return msb;
    }

    static popCount(bb) {
        // Counts the number of set bits (Hamming weight)
        let count = 0;
        while (bb) {
            bb &= bb - 1n;
            count++;
        }
        return count;
    }

    static getFile(square) {
        // Returns file (0-7) for a given square (0-63)
        return square % 8;
    }

    static getRank(square) {
        // Returns rank (0-7) for a given square (0-63)
        return Math.floor(square / 8);
    }

    static squareToAlgebraic(square) {
        // Converts 0-63 index to algebraic notation (e.g., 0 -> 'a1')
        if (square < 0 || square > 63) return '';
        const file = 'abcdefgh'.charAt(square % 8);
        const rank = Math.floor(square / 8) + 1;
        return file + rank;
    }

    static algebraicToSquare(alg) {
        // Converts algebraic notation to 0-63 index (e.g., 'a1' -> 0)
        if (alg.length !== 2) return -1;
        const file = alg.charCodeAt(0) - 'a'.charCodeAt(0);
        const rank = parseInt(alg[1]) - 1;
        if (file < 0 || file > 7 || rank < 0 || rank > 7) return -1;
        return rank * 8 + file;
    }

    static generateRandom64() {
        // Generates a random 64-bit BigInt
        const buf = new BigUint64Array(1);
        crypto.getRandomValues(buf);
        return buf[0];
    }

    static moveToUCI(move) {
        // Converts internal move representation to UCI string
        if (!move) return '0000';
        const from = this.squareToAlgebraic(move.from);
        const to = this.squareToAlgebraic(move.to);
        let promotion = '';
        
        if (move.flags === this.engine.MOVE_FLAGS.PROMOTION) {
            const promoPieces = ['', 'q', 'r', 'b', 'n'];
            promotion = promoPieces[move.promotion] || '';
        }
        
        return from + to + promotion;
    }

    static parseUCIMove(uci) {
        // Parses UCI move string into internal move representation
        if (uci.length < 4) return null;
        
        const from = this.algebraicToSquare(uci.substring(0, 2));
        const to = this.algebraicToSquare(uci.substring(2, 4));
        
        if (from === -1 || to === -1) return null;
        
        let promotion = 0;
        let flags = this.engine.MOVE_FLAGS.NORMAL;
        
        if (uci.length > 4) {
            const promoChar = uci[4].toLowerCase();
            switch (promoChar) {
                case 'q': promotion = this.engine.PIECE_TYPES.QUEEN; break;
                case 'r': promotion = this.engine.PIECE_TYPES.ROOK; break;
                case 'b': promotion = this.engine.PIECE_TYPES.BISHOP; break;
                case 'n': promotion = this.engine.PIECE_TYPES.KNIGHT; break;
                default: return null;
            }
            flags = this.engine.MOVE_FLAGS.PROMOTION;
        }
        
        const piece = this.engine.getPieceAt(from, this.engine.side);
        const captured = this.engine.getPieceAt(to, this.engine.side ^ 1);
        
        return {
            from,
            to,
            piece,
            captured,
            promotion,
            flags,
            score: 0
        };
    }

    static isSlidingPiece(pieceType) {
        // Checks if a piece is a sliding piece (bishop, rook, queen)
        return pieceType === this.engine.PIECE_TYPES.BISHOP ||
               pieceType === this.engine.PIECE_TYPES.ROOK ||
               pieceType === this.engine.PIECE_TYPES.QUEEN;
    }

    static gamePhase(game) {
        // Calculates game phase (0 = opening, 256 = endgame)
        let phase = 256;
        
        // Subtract phase values for each piece type
        const phaseValues = [0, 0, 1, 1, 2, 4, 0];
        
        for (let piece = this.engine.PIECE_TYPES.KNIGHT; piece <= this.engine.PIECE_TYPES.QUEEN; piece++) {
            phase -= this.popCount(game.bitboards[this.engine.COLORS.WHITE * 6 + piece - 1]) * phaseValues[piece];
            phase -= this.popCount(game.bitboards[this.engine.COLORS.BLACK * 6 + piece - 1]) * phaseValues[piece];
        }
        
        return Math.max(0, Math.min(256, phase));
    }

    static getDistance(sq1, sq2) {
        // Returns Chebyshev distance between two squares
        const file1 = this.getFile(sq1);
        const rank1 = this.getRank(sq1);
        const file2 = this.getFile(sq2);
        const rank2 = this.getRank(sq2);
        
        return Math.max(Math.abs(file1 - file2), Math.abs(rank1 - rank2));
    }

    static getDirection(from, to) {
        // Returns direction vector between two squares
        const fileDiff = this.getFile(to) - this.getFile(from);
        const rankDiff = this.getRank(to) - this.getRank(from);
        
        return {
            file: fileDiff !== 0 ? fileDiff / Math.abs(fileDiff) : 0,
            rank: rankDiff !== 0 ? rankDiff / Math.abs(rankDiff) : 0
        };
    }

    static getBetweenMask(from, to) {
        // Returns bitboard of squares between two squares (exclusive)
        if (from === to) return 0n;
        
        const file1 = this.getFile(from);
        const rank1 = this.getRank(from);
        const file2 = this.getFile(to);
        const rank2 = this.getRank(to);
        
        // Not on same line
        if (file1 !== file2 && rank1 !== rank2 && 
            Math.abs(file1 - file2) !== Math.abs(rank1 - rank2)) {
            return 0n;
        }
        
        let mask = 0n;
        const step = this.getDirection(from, to);
        let current = from + step.file + step.rank * 8;
        
        while (current !== to) {
            mask |= 1n << BigInt(current);
            current += step.file + step.rank * 8;
        }
        
        return mask;
    }

    static formatTime(ms) {
        // Formats milliseconds into HH:MM:SS format
        const seconds = Math.floor(ms / 1000);
        const hours = Math.floor(seconds / 3600);
        const minutes = Math.floor((seconds % 3600) / 60);
        const secs = seconds % 60;
        
        return `${hours.toString().padStart(2, '0')}:${minutes.toString().padStart(2, '0')}:${secs.toString().padStart(2, '0')}`;
    }

    static formatScore(score) {
        // Formats evaluation score for UCI output
        if (score >= this.engine.MATE_SCORE) {
            const plyToMate = this.engine.MATE_VALUE - score;
            const movesToMate = Math.ceil(plyToMate / 2);
            return `mate ${movesToMate}`;
        }
        if (score <= -this.engine.MATE_SCORE) {
            const plyToMate = this.engine.MATE_VALUE + score;
            const movesToMate = Math.ceil(plyToMate / 2);
            return `mate -${movesToMate}`;
        }
        return `cp ${Math.round(score)}`;
    }

    static perft(game, depth, divide = false) {
        // Performance test function
        if (depth === 0) return 1;
        
        const moves = game.generateMoves();
        let total = 0;
        const results = {};
        
        for (const move of moves) {
            const undo = game.makeMove(move);
            const count = this.perft(game, depth - 1, false);
            game.undoMove(move, undo);
            
            if (divide) {
                const moveStr = this.moveToUCI(move);
                results[moveStr] = count;
            }
            
            total += count;
        }
        
        if (divide) {
            const sorted = Object.entries(results).sort((a, b) => a[0].localeCompare(b[0]));
            for (const [move, count] of sorted) {
                console.log(`${move}: ${count}`);
            }
        }
        
        return total;
    }
}

module.exports = Helpers;
/////////////////////////////////
// utils/Bitboard.js
class Bitboard {
    constructor(engine) {
        this.engine = engine;
        this.initTables();
    }

    initTables() {
        // Initialize precomputed tables
        this.rays = this.initRayTables();
        this.between = this.initBetweenTables();
        this.line = this.initLineTables();
        this.knightAttacks = this.initKnightAttacks();
        this.kingAttacks = this.initKingAttacks();
        this.pawnAttacks = this.initPawnAttacks();
    }

    // Basic bitboard operations
    setBit(bb, square) {
        return bb | (1n << BigInt(square));
    }

    clearBit(bb, square) {
        return bb & ~(1n << BigInt(square));
    }

    toggleBit(bb, square) {
        return bb ^ (1n << BigInt(square));
    }

    getBit(bb, square) {
        return (bb >> BigInt(square)) & 1n;
    }

    countBits(bb) {
        let count = 0;
        while (bb) {
            bb &= bb - 1n;
            count++;
        }
        return count;
    }

    getLSB(bb) {
        if (bb === 0n) return -1;
        return BigInt.asUintN(64, bb & -bb).toString(2).length - 1;
    }

    getMSB(bb) {
        if (bb === 0n) return -1;
        let msb = 0;
        while (bb > 1n) {
            bb >>= 1n;
            msb++;
        }
        return msb;
    }

    popLSB(bb) {
        const lsb = this.getLSB(bb);
        return [lsb, bb & (bb - 1n)];
    }

    // Bitboard generation
    generateFileMask(file) {
        return 0x0101010101010101n << BigInt(file);
    }

    generateRankMask(rank) {
        return 0xFFn << BigInt(rank * 8);
    }

    generateDiagonalMask(square) {
        const diag = 8 * (this.getRank(square) - this.getFile(square));
        return diag >= 0 ? 
            0x8040201008040201n << BigInt(diag) :
            0x8040201008040201n >> BigInt(-diag);
    }

    generateAntiDiagonalMask(square) {
        const diag = 56 - 8 * (this.getRank(square) + this.getFile(square));
        return diag >= 0 ?
            0x0102040810204080n << BigInt(diag) :
            0x0102040810204080n >> BigInt(-diag);
    }

    // Attack generation
    generateSliderAttacks(square, occupied, pieceType) {
        let attacks = 0n;
        const directions = this.getSliderDirections(pieceType);

        for (const [df, dr] of directions) {
            let f = this.getFile(square) + df;
            let r = this.getRank(square) + dr;
            
            while (f >= 0 && f < 8 && r >= 0 && r < 8) {
                const s = r * 8 + f;
                attacks |= 1n << BigInt(s);
                
                if ((occupied & (1n << BigInt(s))) !== 0n) {
                    break;
                }
                
                f += df;
                r += dr;
            }
        }
        
        return attacks;
    }

    getSliderDirections(pieceType) {
        switch (pieceType) {
            case this.engine.PIECE_TYPES.BISHOP:
                return [[1, 1], [1, -1], [-1, 1], [-1, -1]];
            case this.engine.PIECE_TYPES.ROOK:
                return [[1, 0], [-1, 0], [0, 1], [0, -1]];
            case this.engine.PIECE_TYPES.QUEEN:
                return [[1, 1], [1, -1], [-1, 1], [-1, -1], [1, 0], [-1, 0], [0, 1], [0, -1]];
            default:
                return [];
        }
    }

    // Precomputed tables initialization
    initRayTables() {
        const rays = Array.from({length: 8}, () => new Array(64).fill(0n));
        
        for (let sq = 0; sq < 64; sq++) {
            const f = this.getFile(sq);
            const r = this.getRank(sq);
            
            // North
            for (let i = r + 1; i < 8; i++) {
                rays[0][sq] |= 1n << BigInt(i * 8 + f);
            }
            
            // South
            for (let i = r - 1; i >= 0; i--) {
                rays[1][sq] |= 1n << BigInt(i * 8 + f);
            }
            
            // East
            for (let i = f + 1; i < 8; i++) {
                rays[2][sq] |= 1n << BigInt(r * 8 + i);
            }
            
            // West
            for (let i = f - 1; i >= 0; i--) {
                rays[3][sq] |= 1n << BigInt(r * 8 + i);
            }
            
            // Northeast
            for (let i = 1; f + i < 8 && r + i < 8; i++) {
                rays[4][sq] |= 1n << BigInt((r + i) * 8 + (f + i));
            }
            
            // Northwest
            for (let i = 1; f - i >= 0 && r + i < 8; i++) {
                rays[5][sq] |= 1n << BigInt((r + i) * 8 + (f - i));
            }
            
            // Southeast
            for (let i = 1; f + i < 8 && r - i >= 0; i++) {
                rays[6][sq] |= 1n << BigInt((r - i) * 8 + (f + i));
            }
            
            // Southwest
            for (let i = 1; f - i >= 0 && r - i >= 0; i++) {
                rays[7][sq] |= 1n << BigInt((r - i) * 8 + (f - i));
            }
        }
        
        return rays;
    }

    initBetweenTables() {
        const between = Array.from({length: 64}, () => new Array(64).fill(0n));
        
        for (let a = 0; a < 64; a++) {
            for (let b = 0; b < 64; b++) {
                if (a === b) continue;
                
                const delta = b - a;
                const step = Math.sign(delta);
                
                // Same rank
                if (this.getRank(a) === this.getRank(b)) {
                    for (let i = a + step; i !== b; i += step) {
                        between[a][b] |= 1n << BigInt(i);
                    }
                }
                // Same file
                else if (this.getFile(a) === this.getFile(b)) {
                    for (let i = a + 8 * step; i !== b; i += 8 * step) {
                        between[a][b] |= 1n << BigInt(i);
                    }
                }
                // Same diagonal
                else if (Math.abs(this.getFile(a) - this.getFile(b)) === 
                         Math.abs(this.getRank(a) - this.getRank(b))) {
                    const dir = step * (delta % 8 === 0 ? 8 : 9);
                    for (let i = a + dir; i !== b; i += dir) {
                        between[a][b] |= 1n << BigInt(i);
                    }
                }
            }
        }
        
        return between;
    }

    initLineTables() {
        const line = Array.from({length: 64}, () => new Array(64).fill(0n));
        
        for (let a = 0; a < 64; a++) {
            for (let b = 0; b < 64; b++) {
                if (a === b) continue;
                
                // Same rank
                if (this.getRank(a) === this.getRank(b)) {
                    line[a][b] = this.generateRankMask(this.getRank(a));
                }
                // Same file
                else if (this.getFile(a) === this.getFile(b)) {
                    line[a][b] = this.generateFileMask(this.getFile(a));
                }
                // Same diagonal
                else if (Math.abs(this.getFile(a) - this.getFile(b)) === 
                         Math.abs(this.getRank(a) - this.getRank(b))) {
                    line[a][b] = this.generateDiagonalMask(a) | this.generateAntiDiagonalMask(a);
                }
            }
        }
        
        return line;
    }

    initKnightAttacks() {
        const attacks = new Array(64).fill(0n);
        const deltas = [[2, 1], [2, -1], [-2, 1], [-2, -1], 
                       [1, 2], [1, -2], [-1, 2], [-1, -2]];
        
        for (let sq = 0; sq < 64; sq++) {
            const f = this.getFile(sq);
            const r = this.getRank(sq);
            
            for (const [df, dr] of deltas) {
                const newF = f + df;
                const newR = r + dr;
                
                if (newF >= 0 && newF < 8 && newR >= 0 && newR < 8) {
                    attacks[sq] |= 1n << BigInt(newR * 8 + newF);
                }
            }
        }
        
        return attacks;
    }

    initKingAttacks() {
        const attacks = new Array(64).fill(0n);
        const deltas = [[1, 0], [-1, 0], [0, 1], [0, -1], 
                       [1, 1], [1, -1], [-1, 1], [-1, -1]];
        
        for (let sq = 0; sq < 64; sq++) {
            const f = this.getFile(sq);
            const r = this.getRank(sq);
            
            for (const [df, dr] of deltas) {
                const newF = f + df;
                const newR = r + dr;
                
                if (newF >= 0 && newF < 8 && newR >= 0 && newR < 8) {
                    attacks[sq] |= 1n << BigInt(newR * 8 + newF);
                }
            }
        }
        
        return attacks;
    }

    initPawnAttacks() {
        const attacks = Array.from({length: 2}, () => new Array(64).fill(0n));
        
        for (let sq = 0; sq < 64; sq++) {
            const f = this.getFile(sq);
            const r = this.getRank(sq);
            
            // White pawn attacks
            if (r < 7) {
                if (f > 0) attacks[0][sq] |= 1n << BigInt((r + 1) * 8 + (f - 1));
                if (f < 7) attacks[0][sq] |= 1n << BigInt((r + 1) * 8 + (f + 1));
            }
            
            // Black pawn attacks
            if (r > 0) {
                if (f > 0) attacks[1][sq] |= 1n << BigInt((r - 1) * 8 + (f - 1));
                if (f < 7) attacks[1][sq] |= 1n << BigInt((r - 1) * 8 + (f + 1));
            }
        }
        
        return attacks;
    }

    // Utility functions
    getFile(square) {
        return square % 8;
    }

    getRank(square) {
        return Math.floor(square / 8);
    }

    squareToAlgebraic(square) {
        if (square < 0 || square > 63) return '';
        const file = 'abcdefgh'.charAt(this.getFile(square));
        const rank = this.getRank(square) + 1;
        return file + rank;
    }

    algebraicToSquare(alg) {
        if (alg.length !== 2) return -1;
        const file = alg.charCodeAt(0) - 'a'.charCodeAt(0);
        const rank = parseInt(alg[1]) - 1;
        if (file < 0 || file > 7 || rank < 0 || rank > 7) return -1;
        return rank * 8 + file;
    }

    // Advanced operations
    getLeastValuableAttacker(square, occupied, color) {
        const pawns = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.PAWN - 1];
        if (pawns & this.pawnAttacks[color ^ 1][square]) {
            const from = square + (color === this.engine.COLORS.WHITE ? -8 : 8);
            return { piece: this.engine.PIECE_TYPES.PAWN, from };
        }
        
        const knights = this.engine.bitboards[color * 6 + this.engine.PIECE_TYPES.KNIGHT - 1];
        if (knights & this.knightAttacks[square]) {
            const from = this.getLSB(knights & this.knightAttacks[square]);
            return { piece: this.engine.PIECE_TYPES.KNIGHT, from };
        }
        
        // Continue with bishops, rooks, queens, king
        // ...
        
        return null;
    }

    static rotate45(bb) {
        // Rotates bitboard 45 degrees clockwise
        // Used for diagonal attacks
        // Implementation omitted for brevity
        return bb;
    }

    static rotateAnti45(bb) {
        // Rotates bitboard 45 degrees counter-clockwise
        // Used for anti-diagonal attacks
        // Implementation omitted for brevity
        return bb;
    }
}

module.exports = Bitboard;
/////////////////////////////
// utils/Perft.js
class Perft {
    constructor(engine) {
        this.engine = engine;
        this.helper = new (require('./Helpers'))(engine);
    }

    /**
     * Runs a perft test (performance test) to count nodes at each depth
     * @param {number} depth - Maximum depth to search
     * @param {boolean} divide - Whether to show move breakdown
     * @returns {Object} Results object with node counts and timing
     */
    async run(depth, divide = false) {
        const startTime = Date.now();
        const results = {
            totalNodes: 0,
            timeMs: 0,
            nodesPerSec: 0,
            breakdown: {},
            depths: []
        };

        for (let d = 1; d <= depth; d++) {
            const depthStart = Date.now();
            const count = divide ? 
                this.perftDivide(d, results.breakdown) : 
                this.perft(d);
            
            const depthTime = Date.now() - depthStart;
            
            results.depths.push({
                depth: d,
                nodes: count,
                timeMs: depthTime,
                nodesPerSec: Math.floor(count / (depthTime / 1000))
            });
            
            results.totalNodes += count;
        }

        results.timeMs = Date.now() - startTime;
        results.nodesPerSec = Math.floor(results.totalNodes / (results.timeMs / 1000));

        return results;
    }

    /**
     * Basic perft implementation without move breakdown
     * @param {number} depth - Depth to search
     * @returns {number} Node count
     */
    perft(depth) {
        if (depth === 0) return 1;

        const moves = this.engine.generateMoves();
        let nodes = 0;

        for (const move of moves) {
            const undo = this.engine.makeMove(move);
            nodes += this.perft(depth - 1);
            this.engine.undoMove(move, undo);
        }

        return nodes;
    }

    /**
     * Perft with move breakdown
     * @param {number} depth - Depth to search
     * @param {Object} breakdown - Object to store move counts
     * @returns {number} Node count
     */
    perftDivide(depth, breakdown = {}) {
        if (depth === 0) return 1;

        const moves = this.engine.generateMoves();
        let totalNodes = 0;

        for (const move of moves) {
            const undo = this.engine.makeMove(move);
            const moveStr = this.helper.moveToUCI(move);
            
            const nodes = depth === 1 ? 1 : this.perftDivide(depth - 1);
            breakdown[moveStr] = nodes;
            totalNodes += nodes;
            
            this.engine.undoMove(move, undo);
        }

        return totalNodes;
    }

    /**
     * Bulk-counting perft (optimized for speed)
     * @param {number} depth - Depth to search
     * @returns {number} Node count
     */
    perftBulk(depth) {
        if (depth === 0) return 1;
        if (depth === 1) return this.engine.generateMoves().length;

        const moves = this.engine.generateMoves();
        let nodes = 0;

        for (const move of moves) {
            const undo = this.engine.makeMove(move);
            nodes += this.perftBulk(depth - 1);
            this.engine.undoMove(move, undo);
        }

        return nodes;
    }

    /**
     * Asynchronous perft that can be stopped
     * @param {number} depth - Depth to search
     * @param {Function} callback - Progress callback
     * @returns {Promise<number>} Node count
     */
    async perftAsync(depth, callback = null) {
        if (this.engine.stopPerft) {
            this.engine.stopPerft = false;
            return 0;
        }

        if (depth === 0) return 1;

        const moves = this.engine.generateMoves();
        let nodes = 0;
        let moveCount = 0;

        for (const move of moves) {
            if (this.engine.stopPerft) break;

            const undo = this.engine.makeMove(move);
            const childNodes = await this.perftAsync(depth - 1, callback);
            nodes += childNodes;
            this.engine.undoMove(move, undo);

            moveCount++;
            if (callback) {
                callback({
                    depth,
                    currentMove: moveCount,
                    totalMoves: moves.length,
                    nodes
                });
            }

            // Yield to event loop
            if (depth > 3) await new Promise(resolve => setImmediate(resolve));
        }

        return nodes;
    }

    /**
     * Verifies perft results against known positions
     * @returns {Object} Verification results
     */
    verify() {
        const testPositions = [
            {
                fen: 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1',
                results: [20, 400, 8902, 197281, 4865609, 119060324]
            },
            {
                fen: 'r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1',
                results: [48, 2039, 97862, 4085603, 193690690]
            },
            {
                fen: '8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1',
                results: [14, 191, 2812, 43238, 674624, 11030083]
            },
            {
                fen: 'r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1',
                results: [6, 264, 9467, 422333, 15833292]
            },
            {
                fen: 'rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8',
                results: [44, 1486, 62379, 2103487, 89941194]
            }
        ];

        const verificationResults = [];
        const maxDepth = 4; // Limit depth for verification tests

        for (const position of testPositions) {
            this.engine.setPosition(position.fen);
            const result = {
                fen: position.fen,
                expected: position.results.slice(0, maxDepth),
                actual: [],
                passed: true
            };

            for (let depth = 1; depth <= maxDepth; depth++) {
                const nodes = this.perftBulk(depth);
                result.actual.push(nodes);
                
                if (nodes !== position.results[depth - 1]) {
                    result.passed = false;
                }
            }

            verificationResults.push(result);
        }

        return verificationResults;
    }

    /**
     * Formats perft results for display
     * @param {Object} results - Perft results object
     * @returns {string} Formatted string
     */
    formatResults(results) {
        let output = `Total nodes: ${results.totalNodes.toLocaleString()}\n`;
        output += `Total time: ${this.helper.formatTime(results.timeMs)}\n`;
        output += `Nodes/sec: ${results.nodesPerSec.toLocaleString()}\n\n`;
        
        output += 'Depth breakdown:\n';
        output += 'Depth   Nodes           Time     Nodes/sec\n';
        output += '-----   ------------    ------   ------------\n';
        
        for (const depth of results.depths) {
            output += `${depth.depth.toString().padStart(5)}   `;
            output += `${depth.nodes.toLocaleString().padStart(12)}    `;
            output += `${this.helper.formatTime(depth.timeMs)}   `;
            output += `${depth.nodesPerSec.toLocaleString().padStart(12)}\n`;
        }

        if (Object.keys(results.breakdown).length > 0) {
            output += '\nMove breakdown:\n';
            for (const [move, nodes] of Object.entries(results.breakdown)) {
                output += `${move}: ${nodes.toLocaleString()}\n`;
            }
        }

        return output;
    }

    /**
     * Formats verification results for display
     * @param {Object[]} results - Verification results
     * @returns {string} Formatted string
     */
    formatVerification(results) {
        let output = 'Perft Verification Results:\n';
        output += '========================================\n';

        for (const test of results) {
            output += `Position: ${test.fen}\n`;
            
            for (let i = 0; i < test.expected.length; i++) {
                const passed = test.expected[i] === test.actual[i];
                output += `Depth ${i + 1}: ${test.actual[i].toLocaleString()}`;
                output += ` (Expected: ${test.expected[i].toLocaleString()}) `;
                output += passed ? '✓' : '✗';
                output += '\n';
            }
            
            output += `Test ${test.passed ? 'PASSED' : 'FAILED'}\n`;
            output += '----------------------------------------\n';
        }

        return output;
    }
}

module.exports = Perft;
//////////////////////////



//////////////////


// Initialize the engine and UCI interface
const engine = new SKY5LChess();
engine.init().then(() => {
    if (typeof process !== 'undefined' || typeof postMessage !== 'undefined') {
        new UCIInterface(engine);
    }
});


///////////////////////////
// Export for Node.js and browser
if (typeof module !== 'undefined') module.exports = SKY5LChess;
if (typeof window !== 'undefined') window.SKY5LChess = SKY5LChess;
