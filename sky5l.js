// === Reorganized sky5l.js ===

// === Spinner Control ===
// === Spinner Control ===
function showSpinner() {
function hideSpinner() {

// === Game Initialization ===
   const ChessGame = {
            // Initialize chess components
            board: null,
            game: new Chess(),
            moveHistory: [], // Stores all FEN positions
            currentMoveIndex: 0, // Tracks current position in history
            userColor: "white",
            level: "9",
                                const game = new Chess();
                                if (game.load_pgn(pgn)) {
                                    const headers = game.header();
                                    games.push({
                                        white: headers.White || "Unknown",
                                        black: headers.Black || "Unknown",
                                        result: headers.Result || "*",
                                        event: headers.Event || "Unknown",
                                        date: headers.Date || "????.??.??",
                                        pgn: pgn
                                    });
                                }
                            } catch (e) {
                                console.error("Error parsing PGN:", e);
                            }
                        });

                        filesProcessed++;
                        if (filesProcessed === files.length) {
                            if (games.length > 0) {
                    const tempGame = new Chess();
                    const moves = this.game.history({verbose: true});
                    let evaluations = [];
                    let moveLabels = [];
                    let bestMoves = [];
                    let keyMoments = [];
                    
                    // Add initial position evaluation
                const tempGame = new Chess();
                let openingName = "Unknown Opening";
                let openingMoves = [];
                
                // Replay moves to find opening
                for (const move of this.game.history()) {
                    tempGame.move(move);
                    const fen = tempGame.fen().split(' ')[0]; // Get position part of FEN
                    
                    if (this.openingBook[fen]) {
                        const moveSan = tempGame.history().slice(-1)[0];
                        const moveUci = this.sanToUci(tempGame, moveSan);
                        
                        if (this.openingBook[fen][moveUci]) {
                            openingName = this.openingBook[fen][moveUci].name;
                            openingMoves = tempGame.history();
                        }
                    }
                }
                
                return `
                    <p><strong>${openingName}</strong></p>
                    ${openingMoves.length > 0 ? 
                        `<p>Moves: ${openingMoves.join(' ')}</p>` : 
                        '<p>No recognized opening sequence</p>'}
                `;
            },
            
            // Convert SAN move to UCI notation
            sanToUci: function(game, san) {
                const move = game.move(san, {sloppy: true});
                game.undo();
                return move ? move.from + move.to + (move.promotion || '') : '';
            },
            
            // Create evaluation chart
            createEvaluationChart: function(evaluations, moveLabels) {
                        this.game = new Chess();
                        break;
                    case "960":
                        this.game = new Chess();
                        // Generate a random Chess960 position
                        const position = this.generateChess960Position();
                        this.game.load(position);
                        break;
                    case "atomic":
                        this.game = new Chess();
                        break;
                    case "kingofthehill":
                        this.game = new Chess();
                        break;
                    case "threecheck":
                        this.game = new Chess();
                        break;
                    case "horde":
                        this.game = new Chess();
                        // Set up horde position (white pawns on ranks 4-6)
                        this.game.clear();
                        // Set up black pieces normally
                        this.game.put({ type: 'r', color: 'b' }, 'a8');
                        this.game.put({ type: 'n', color: 'b' }, 'b8');
                        this.game.put({ type: 'b', color: 'b' }, 'c8');
                        this.game.put({ type: 'q', color: 'b' }, 'd8');
                        this.game.put({ type: 'k', color: 'b' }, 'e8');
                        this.game.put({ type: 'b', color: 'b' }, 'f8');
                        this.game.put({ type: 'n', color: 'b' }, 'g8');
                        this.game.put({ type: 'r', color: 'b' }, 'h8');
                        for (let i = 0; i < 8; i++) {
                            this.game.put({ type: 'p', color: 'b' }, String.fromCharCode(97 + i) + '7');
                        }
                        // Set up white horde
                        for (let i = 0; i < 8; i++) {
                            this.game.put({ type: 'p', color: 'w' }, String.fromCharCode(97 + i) + '4');
                            this.game.put({ type: 'p', color: 'w' }, String.fromCharCode(97 + i) + '5');
                            this.game.put({ type: 'p', color: 'w' }, String.fromCharCode(97 + i) + '6');
                        }
                        break;
                    case "racingkings":
                        this.game = new Chess();
                        // Set up racing kings position
                        this.game.clear();
                        // White pieces
                        this.game.put({ type: 'k', color: 'w' }, 'e1');
                        this.game.put({ type: 'r', color: 'w' }, 'a1');
                        this.game.put({ type: 'r', color: 'w' }, 'h1');
                        this.game.put({ type: 'n', color: 'w' }, 'b1');
                        this.game.put({ type: 'n', color: 'w' }, 'g1');
                        this.game.put({ type: 'b', color: 'w' }, 'c1');
                        this.game.put({ type: 'b', color: 'w' }, 'f1');
                        this.game.put({ type: 'q', color: 'w' }, 'd1');
                        // Black pieces
                        this.game.put({ type: 'k', color: 'b' }, 'e8');
                        this.game.put({ type: 'r', color: 'b' }, 'a8');
                        this.game.put({ type: 'r', color: 'b' }, 'h8');
                        this.game.put({ type: 'n', color: 'b' }, 'b8');
                        this.game.put({ type: 'n', color: 'b' }, 'g8');
                        this.game.put({ type: 'b', color: 'b' }, 'c8');
                        this.game.put({ type: 'b', color: 'b' }, 'f8');
                        this.game.put({ type: 'q', color: 'b' }, 'd8');
                        break;
                    default:
                        this.game = new Chess();
                }
                
                // Initialize board
                this.board.position(this.game.fen());
                this.moveHistory = [this.game.fen()];
                this.currentMoveIndex = 0;
                
                // Set up clock if needed
                this.setupClock();
                
                // Set user color based on game mode
                if (this.gameMode === "humanVsAI") {
                    this.userColor = "white"; // Human plays white by default
                } else if (this.gameMode === "aiVsAI") {
                    // Start AI vs AI game
                this.game = new Chess();
                this.board = Chessboard('myBoard', this.configs.start);
                this.board.start();
                this.moveHistory = [this.game.fen()];
                this.currentMoveIndex = 0;
                
                const newGame = new Chess();
                
                // First try standard PGN import
                if (!newGame.load_pgn(pgnText)) {
                    // If standard import fails, try more flexible parsing
                    const cleanedPgn = pgnText.replace(/\r?\n/g, " ").replace(/\s+/g, " ").trim();
                    if (!newGame.load_pgn(cleanedPgn)) {
                        throw new Error("Invalid PGN format");
                    }
                }
                
                // Reset game state
                this.resetGameState();
                
                // Replay all moves to build history
                const tempGame = new Chess();
                if (newGame.header()?.FEN) {
                    tempGame.load(newGame.header().FEN);
                }
                this.moveHistory = [tempGame.fen()];
                
                // Load the PGN moves
                const moves = newGame.history({verbose: true});
                for (const move of moves) {
                    const result = tempGame.move(move);
                    if (!result) {
                        throw new Error("Invalid move in PGN: " + move.san);
                    }
                    this.moveHistory.push(tempGame.fen());
                }
                this.currentMoveIndex = this.moveHistory.length - 1;
                
                // Update game state
                this.game = new Chess(this.moveHistory[this.currentMoveIndex]);
                
                // Update UI
                this.board.position(this.game.fen());
                this.updateUIAfterImport();
            },
            
            handleMultiGameImport: function(pgnText) {
                // Normalize line endings and clean up the PGN
                const normalizedPgn = pgnText.replace(/\r\n/g, "\n").replace(/\r/g, "\n");
                const gameSections = normalizedPgn.split(/\n\n(?=\[)/);
                let validGames = 0;
                const games = [];
                
                for (const gameText of gameSections) {
                    const trimmedText = gameText.trim();
                    if (!trimmedText) continue;
                    
                    try {
                        const tempGame = new Chess();
                        if (tempGame.load_pgn(trimmedText)) {
                            const headers = tempGame.header();
                            games.push({
                                pgn: trimmedText,
                                white: headers.White || "Unknown",
                                black: headers.Black || "Unknown",
                                result: headers.Result || "*",
                                event: headers.Event || "Unknown",
                                date: headers.Date || "????.??.??",
                                site: headers.Site || "Unknown",
                                round: headers.Round || "?",
                                fen: headers.FEN || null
                            });
                            validGames++;
                        }
                    } catch (e) {
                        console.warn("Skipping invalid PGN game:", e.message);
                    }
                }

                if (validGames > 0) {
                    this.databaseGames = games;
                    this.updateDatabaseList();

// === Variant Handlers ===
function handleVariantMove(move) {
    switch (ChessGame.gameVariant) {
        case 'threecheck':
            handleThreeCheck(move);
            break;
        case 'crazyhouse':
            handleCrazyhouseMove(move);
            break;
        case 'antichess':
            handleAntichessMove(move);
            break;
        case 'chessgi':
            applyChessGIRules();
            break;
    }
}


                    case 'horde':
                        if (kings.white !== 0) return { valid: false, message: "Horde: White must have no king" };
                        break;
                    case 'racingkings':
                        const kingPos = this.getKingPositions();
                        if (kingPos.white[1] !== '1' || kingPos.black[1] !== '1') 
                            return { valid: false, message: "Racing Kings: Kings must start on 1st rank" };
                        break;
                    default:
                        if (kings.white !== 1 || kings.black !== 1) 
                            return { valid: false, message: "Need exactly 1 white and 1 black king" };
                        if (this.areSquaresAdjacent(this.getKingPositions().white, this.getKingPositions().black))
                            return { valid: false, message: "Kings cannot be adjacent" };
                }

                if (this.hasInvalidPawns()) 
                    return { valid: false, message: "Pawns cannot be on first/last rank" };
                
                return { valid: true, message: "Position is valid" };
            },
            
            // Helper function to count kings
            countKings: function() {
                const board = this.game.board();
                let whiteKings = 0, blackKings = 0;
                
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece && piece.type === 'k') {
                            if (piece.color === 'w') whiteKings++;
                            else blackKings++;
                        }
                    }
                }
                
                return { white: whiteKings, black: blackKings };
            },
            
            // Helper function to get king positions
            getKingPositions: function() {
                const board = this.game.board();
                let whiteKing = null, blackKing = null;
                
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece && piece.type === 'k') {
                            const square = String.fromCharCode(97 + j) + (8 - i);
                            if (piece.color === 'w') whiteKing = square;
                            else blackKing = square;
                        }
                    }
                }
                
                return { white: whiteKing, black: blackKing };
            },
            
            // Helper function to check if squares are adjacent
            areSquaresAdjacent: function(square1, square2) {
                if (!square1 || !square2) return false;
                
                const file1 = square1.charCodeAt(0) - 97;
                const rank1 = parseInt(square1[1]);
                const file2 = square2.charCodeAt(0) - 97;
                const rank2 = parseInt(square2[1]);
                
                return Math.abs(file1 - file2) <= 1 && Math.abs(rank1 - rank2) <= 1;
            },
            
            // Helper function to check for invalid pawns
            hasInvalidPawns: function() {
                const board = this.game.board();
                
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece && piece.type === 'p') {
                            const rank = 8 - i;
                            if ((piece.color === 'w' && rank === 8) || 
                                (piece.color === 'b' && rank === 1)) {
                                return true;
                            }
                        }
                    }
                }
                
                return false;
            },
            
            // Variant move handlers
            handleAtomicMove: function(move) {
                if (!move.captured) return;
                
                // Show explosion effect

// === UI Controls ===
    const overlay = document.getElementById("loadingOverlay");
    if (overlay) overlay.style.display = "flex";
}

    const overlay = document.getElementById("loadingOverlay");
    if (overlay) overlay.style.display = "none";
}

// Injected: Variant dispatcher
                document.getElementById("myBoard").appendChild(arrowLayer);
            },
            
            // Piece theme function
            pieceTheme: function(piece) {
                // Default piece set
                if (this.currentPieceTheme === "default") {
                    if (piece === "bB") return "https://upload.wikimedia.org/wikipedia/commons/9/98/Chess_bdt45.svg";
                    if (piece === "bK") return "https://upload.wikimedia.org/wikipedia/commons/f/f0/Chess_kdt45.svg";
                    if (piece === "bN") return "https://upload.wikimedia.org/wikipedia/commons/e/ef/Chess_ndt45.svg";
                    if (piece === "bP") return "https://upload.wikimedia.org/wikipedia/commons/c/c7/Chess_pdt45.svg";
                    if (piece === "bQ") return "https://upload.wikimedia.org/wikipedia/commons/4/47/Chess_qdt45.svg";
                    if (piece === "bR") return "https://upload.wikimedia.org/wikipedia/commons/f/ff/Chess_rdt45.svg";
                    if (piece === "wB") return "https://upload.wikimedia.org/wikipedia/commons/b/b1/Chess_blt45.svg";
                    if (piece === "wK") return "https://upload.wikimedia.org/wikipedia/commons/4/42/Chess_klt45.svg";
                    if (piece === "wN") return "https://upload.wikimedia.org/wikipedia/commons/7/70/Chess_nlt45.svg";
                    if (piece === "wP") return "https://upload.wikimedia.org/wikipedia/commons/4/45/Chess_plt45.svg";
                    if (piece === "wQ") return "https://upload.wikimedia.org/wikipedia/commons/1/15/Chess_qlt45.svg";
                    if (piece === "wR") return "https://upload.wikimedia.org/wikipedia/commons/7/72/Chess_rlt45.svg";
                }
                // Alpha piece set
                else if (this.currentPieceTheme === "alpha") {
                    if (piece === "bB") return "https://upload.wikimedia.org/wikipedia/commons/8/81/Chess_bdt60.png";
                    if (piece === "bK") return "https://upload.wikimedia.org/wikipedia/commons/e/e3/Chess_kdt60.png";
                    if (piece === "bN") return "https://upload.wikimedia.org/wikipedia/commons/2/28/Chess_ndt60.png";
                    if (piece === "bP") return "https://upload.wikimedia.org/wikipedia/commons/c/cd/Chess_pdt60.png";
                    if (piece === "bQ") return "https://upload.wikimedia.org/wikipedia/commons/a/a0/Chess_qdt60.png";
                    if (piece === "bR") return "https://upload.wikimedia.org/wikipedia/commons/3/3c/Chess_rdt60.png";
                    if (piece === "wB") return "https://upload.wikimedia.org/wikipedia/commons/9/9b/Chess_blt60.png";
                    if (piece === "wK") return "https://upload.wikimedia.org/wikipedia/commons/3/3b/Chess_klt60.png";
                    if (piece === "wN") return "https://upload.wikimedia.org/wikipedia/commons/2/2f/Chess_nlt60.png";
                    if (piece === "wP") return "https://upload.wikimedia.org/wikipedia/commons/0/04/Chess_plt60.png";
                    if (piece === "wQ") return "https://upload.wikimedia.org/wikipedia/commons/4/49/Chess_qlt60.png";
                    if (piece === "wR") return "https://upload.wikimedia.org/wikipedia/commons/5/5c/Chess_rlt60.png";
                }
                // Leipzig piece set
                else if (this.currentPieceTheme === "leipzig") {
                    if (piece === "bB") return "https://upload.wikimedia.org/wikipedia/commons/8/81/Chess_bdt60.png";
                    if (piece === "bK") return "https://upload.wikimedia.org/wikipedia/commons/e/e3/Chess_kdt60.png";
                    if (piece === "bN") return "https://upload.wikimedia.org/wikipedia/commons/2/28/Chess_ndt60.png";
                    if (piece === "bP") return "https://upload.wikimedia.org/wikipedia/commons/c/cd/Chess_pdt60.png";
                    if (piece === "bQ") return "https://upload.wikimedia.org/wikipedia/commons/a/a0/Chess_qdt60.png";
                    if (piece === "bR") return "https://upload.wikimedia.org/wikipedia/commons/3/3c/Chess_rdt60.png";
                    if (piece === "wB") return "https://upload.wikimedia.org/wikipedia/commons/9/9b/Chess_blt60.png";
                    if (piece === "wK") return "https://upload.wikimedia.org/wikipedia/commons/3/3b/Chess_klt60.png";
                    if (piece === "wN") return "https://upload.wikimedia.org/wikipedia/commons/2/2f/Chess_nlt60.png";
                    if (piece === "wP") return "https://upload.wikimedia.org/wikipedia/commons/0/04/Chess_plt60.png";
                    if (piece === "wQ") return "https://upload.wikimedia.org/wikipedia/commons/4/49/Chess_qlt60.png";
                    if (piece === "wR") return "https://upload.wikimedia.org/wikipedia/commons/5/5c/Chess_rlt60.png";
                }
                // Merida piece set
                else if (this.currentPieceTheme === "merida") {
                    if (piece === "bB") return "https://upload.wikimedia.org/wikipedia/commons/8/81/Chess_bdt60.png";
                    if (piece === "bK") return "https://upload.wikimedia.org/wikipedia/commons/e/e3/Chess_kdt60.png";
                    if (piece === "bN") return "https://upload.wikimedia.org/wikipedia/commons/2/28/Chess_ndt60.png";
                    if (piece === "bP") return "https://upload.wikimedia.org/wikipedia/commons/c/cd/Chess_pdt60.png";
                    if (piece === "bQ") return "https://upload.wikimedia.org/wikipedia/commons/a/a0/Chess_qdt60.png";
                    if (piece === "bR") return "https://upload.wikimedia.org/wikipedia/commons/3/3c/Chess_rdt60.png";
                    if (piece === "wB") return "https://upload.wikimedia.org/wikipedia/commons/9/9b/Chess_blt60.png";
                    if (piece === "wK") return "https://upload.wikimedia.org/wikipedia/commons/3/3b/Chess_klt60.png";
                    if (piece === "wN") return "https://upload.wikimedia.org/wikipedia/commons/2/2f/Chess_nlt60.png";
                    if (piece === "wP") return "https://upload.wikimedia.org/wikipedia/commons/0/04/Chess_plt60.png";
                    if (piece === "wQ") return "https://upload.wikimedia.org/wikipedia/commons/4/49/Chess_qlt60.png";
                    if (piece === "wR") return "https://upload.wikimedia.org/wikipedia/commons/5/5c/Chess_rlt60.png";
                }
                return "";
            },
            
            // Chessboard.js configurations
            configs: {
                start: {
                    pieceTheme: (piece) => ChessGame.pieceTheme(piece),
                    draggable: true,
                    dropOffBoard: "trash",
                    onDragStart: (source, piece) => ChessGame.onDragStart(source, piece),
                    onDrop: (source, target) => ChessGame.onDrop(source, target),
                    onMouseoutSquare: (square, piece) => ChessGame.onMouseoutSquare(square, piece),
                    onMouseoverSquare: (square, piece) => ChessGame.onMouseoverSquare(square, piece),
                    onSnapEnd: () => ChessGame.onSnapEnd(),
                    showNotation: false,
                    onPromotionDialog: (source, target, callback) => ChessGame.onPromotionDialog(source, target, callback)
                },
                edit: {
                    pieceTheme: (piece) => ChessGame.pieceTheme(piece),
                    draggable: true,
                    dropOffBoard: "trash",
                    sparePieces: true,
                    showNotation: false
                }
            },
            
            // Initialize the chessboard
            initializeBoard: function() {
                this.board = Chessboard('myBoard', this.configs.start);
                this.board.start();
                this.moveHistory.push(this.game.fen()); // Initial position
                this.updateMoveList();
            },
            
            // Initialize Bootstrap Table for database
            initializeDatabaseTable: function() {
                const ctx = document.getElementById('analysisChart').getContext('2d');
                
                // Destroy previous chart if it exists
                if (this.analysisChart) {
                    this.analysisChart.destroy();
                }
                
                this.analysisChart = new Chart(ctx, {
                    type: 'line',
                    data: {
                        labels: moveLabels,
                        datasets: [{
                            label: 'Evaluation',
                            data: evaluations,
                            borderColor: '#7fa650',
                            backgroundColor: 'rgba(127, 166, 80, 0.1)',
                            borderWidth: 2,
                            pointBackgroundColor: (ctx) => {
                                const value = ctx.dataset.data[ctx.dataIndex];
                                return value > 0 ? '#f0d9b5' : '#b58863';
                            },
                            pointRadius: 4,
                            pointHoverRadius: 6,
                            fill: true,
                            tension: 0.1
                        }]
                    },
                    options: {
                        responsive: true,
                        maintainAspectRatio: false,
                        scales: {
                            y: {
                                beginAtZero: false,
                                ticks: {
                                    callback: function(value) {
                                        return value > 0 ? '+' + value.toFixed(1) : value.toFixed(1);
                                    }
                                },
                                grid: {
                                    color: '#444'
                                }
                            },
                            x: {
                                grid: {
                                    color: '#444'
                                }
                            }
                        },
                        plugins: {
                            legend: {
                                display: false
                            },
                            tooltip: {
                                callbacks: {
                                    label: function(context) {
                                        const value = context.parsed.y;
                                        return value > 0 ? '+' + value.toFixed(1) : value.toFixed(1);
                                    }
                                }
                            }
                        },
                        onClick: (e, elements) => {
                            if (elements.length > 0) {
                                const index = elements[0].index;
                                if (index < this.moveHistory.length) {
                                    this.game.load(this.moveHistory[index]);
                                    this.board.position(this.moveHistory[index]);
                                }
                            }
                        }
                    }
                });
            },
            
            
            // Draw arrow on board
            drawArrow: function(from, to, color = "rgba(255,0,0,0.6)") {
                const ctx = document.getElementById("arrowLayer").getContext("2d");
                const boardSize = document.getElementById("arrowLayer").width = 
                    document.getElementById("arrowLayer").height = 
                    document.getElementById("myBoard").offsetWidth;
                ctx.clearRect(0, 0, boardSize, boardSize);
                const squareSize = boardSize / 8;
                const f = [from.charCodeAt(0) - 97, 8 - parseInt(from[1])];
                const t = [to.charCodeAt(0) - 97, 8 - parseInt(to[1])];
                ctx.strokeStyle = color;
                ctx.lineWidth = 5;
                ctx.beginPath();
                ctx.moveTo((f[0] + 0.5) * squareSize, (f[1] + 0.5) * squareSize);
                ctx.lineTo((t[0] + 0.5) * squareSize, (t[1] + 0.5) * squareSize);
                
                // Draw arrowhead
                const angle = Math.atan2(t[1] - f[1], t[0] - f[0]);
                ctx.lineTo(
                    (t[0] + 0.5) * squareSize - 10 * Math.cos(angle - Math.PI / 6),
                    (t[1] + 0.5) * squareSize - 10 * Math.sin(angle - Math.PI / 6)
                );
                ctx.moveTo((t[0] + 0.5) * squareSize, (t[1] + 0.5) * squareSize);
                ctx.lineTo(
                    (t[0] + 0.5) * squareSize - 10 * Math.cos(angle + Math.PI / 6),
                    (t[1] + 0.5) * squareSize - 10 * Math.sin(angle + Math.PI / 6)
                );
                
                ctx.stroke();
            },
            
                const arrowLayer = document.getElementById("arrowLayer");
                if (arrowLayer) {
                    arrowLayer.getContext("2d").clearRect(0, 0, arrowLayer.width, arrowLayer.height);
                }
                
                this.updateMoveList();
            },
            
            getGameResult: function() {
                if (!this.game) return "*";
                
                if (this.game.in_checkmate()) {
                    return this.game.turn() === 'w' ? "0-1" : "1-0";
                }
                if (this.game.in_draw()) {
                    if (this.game.in_stalemate()) return "1/2-1/2";
                    if (this.game.in_threefold_repetition()) return "1/2-1/2";
                    if (this.game.insufficient_material()) return "1/2-1/2";
                    if (this.game.in_50move_rule()) return "1/2-1/2";
                    return "1/2-1/2";
                }
                return "*";
            },
            
            // Get game result message
            getGameResultMessage: function() {
                if (this.game.in_checkmate()) {
                    return this.game.turn() === 'w' ? "Black wins by checkmate" : "White wins by checkmate";
                }
                if (this.game.in_draw()) {
                    if (this.game.in_stalemate()) return "Game drawn by stalemate";
                    if (this.game.in_threefold_repetition()) return "Game drawn by threefold repetition";
                    if (this.game.insufficient_material()) return "Game drawn by insufficient material";
                    if (this.game.in_50move_rule()) return "Game drawn by 50-move rule";
                    return "Game drawn";
                }
                return "Game over";
            },
            
            // Toggle PGN options
            togglePgnOptions: function() {

// === PGN Handling ===


// === Engine Communication ===
            isEngineSolving: false,
            isEditing: false,
            databaseGames: [],
            currentDatabaseGame: null,
            aiSolvingSide: null,
            promotionMove: null,
            currentEngine: "sunfish",
            panelVisible: false,
            clockInterval: null,
            whiteTime: 600, // 10 minutes in seconds
            blackTime: 600, // 10 minutes in seconds
            currentClockType: "none",
            gameVariant: "standard",
            gameMode: "humanVsHuman",
            isHintActive: false,
            currentEngineInfo: {},
            puzzleMode: false,
            currentPuzzle: null,
            userMoves: [],
            evaluationCache: {},
            analysisChart: null,
            openingBook: {},
            transpositionTable: {},
            currentTheme: "default",
            currentPieceTheme: "default",
            
            // Initialize the game
            init: function() {
                this.createArrowLayer();
                this.setupEventHandlers();
                this.initializeBoard();
                this.initializeDatabaseTable();
                this.checkLoginStatus();
                this.loadOpeningBook();
                
                // Clean up when page unloads
            // Request best move from engine using Web Worker if available
            requestBestMove: function(depth = 3) {
                this.showLoading();
                
                // Use setTimeout to allow UI to update before heavy computation
                setTimeout(() => {
                    try {
                        const move = Sky5lEngine.get_best_move(this.game.fen(), depth);
                        if (this.isHintActive) {
                            this.showHintMove(move.from + move.to + (move.promotion || ''));
                            this.isHintActive = false;
                        } else if (this.isEngineSolving) {
                            this.handleEngineMove(move.from + move.to + (move.promotion || ''));
                        }
                    } catch (e) {
                        console.error("Engine error:", e);
                        this.displayHint("Engine error: " + e.message);
                    } finally {
                        this.hideLoading();
                    }
                }, 50);
            },
            
            // Handle puzzle moves
            handlePuzzleMove: function(bestMove) {
                if (!this.currentPuzzle) return;
                
                // Record user move
                const lastMove = this.game.history({verbose: true}).pop();
                if (lastMove) {
                    const userMove = lastMove.from + lastMove.to + (lastMove.promotion || '');
                    this.userMoves.push(userMove);
                }
                
                // Check if user found the solution
                if (this.userMoves.join(" ") === this.currentPuzzle.join(" ")) {
                    this.displayHint("Puzzle solved! Congratulations!");
                    this.puzzleMode = false;
                    return;
                }
                
                // Check if user made the correct move
                const expectedMove = this.currentPuzzle[this.userMoves.length - 1];
                if (bestMove === expectedMove) {
                    this.displayHint("Correct! Now find the next move.");
                } else {
                    this.displayHint("Not the best move. Try again!");
                    this.stepBack();
                }
            },
            
            // Load random puzzle
            loadRandomPuzzle: function() {
                this.showLoading();
                
                // In a real implementation, this would fetch from a server
                setTimeout(() => {
                    const puzzles = [
                        {
                            fen: "r1bqkb1r/pppp1Qpp/2n2n2/4p3/2B1P3/8/PPPP1PPP/RNB1K1NR b KQkq - 0 1",
                            solution: ["f6f7", "e8f7", "c4f7"],
                            description: "Mate in 3 - Queen sacrifice"
                        },
                        {
                            fen: "r1bq1rk1/pppp1ppp/2n2n2/4p3/1bB1P3/2N2N2/PPPP1PPP/R1BQ1RK1 w - - 0 1",
                            solution: ["c3d5", "f6d5", "c4d5"],
                            description: "Fork the king and rook"
                        },
                        {
                            fen: "8/8/8/5N1k/8/8/3K4/8 b - - 0 1",
                            solution: ["h5h6", "d2e3", "h6g5"],
                            description: "King and knight endgame"
                        }
                    ];
                    
                    const puzzle = puzzles[Math.floor(Math.random() * puzzles.length)];
                    this.startPuzzle(puzzle.fen, puzzle.solution, puzzle.description);
                    this.hideLoading();
                }, 100);
            },
            
            // Start puzzle mode with description
            startPuzzle: function(fen, solutionMoves, description = "Solve the puzzle!") {
                this.puzzleMode = true;
                this.currentPuzzle = solutionMoves;
                this.userMoves = [];
                this.game.load(fen);
                this.board.position(fen);
                this.moveHistory = [this.game.fen()];
                this.currentMoveIndex = 0;
                this.displayHint(description);
                
                // Add puzzle indicator
                    const initialEval = Sky5lEngine.evaluate(tempGame);
                    evaluations.push(initialEval);
                    moveLabels.push("Start");
                    bestMoves.push("-");
                    
                    // Analyze each move
                    for (let i = 0; i < moves.length; i++) {
                        const move = moves[i];
                        tempGame.move(move);
                        
                        // Get evaluation after this move
                        const evalAfter = Sky5lEngine.evaluate(tempGame);
                        evaluations.push(evalAfter);
                        
                        // Find best move from this position
                        const bestMove = Sky5lEngine.get_best_move(tempGame.fen(), 3);
                        const bestMoveSan = bestMove ? tempGame.move(bestMove).san : 'N/A';
                        if (bestMove) tempGame.undo();
                        
                        moveLabels.push(`${i+1}. ${move.san}`);
                        bestMoves.push(bestMoveSan);
                        
                        // Check for key moments (big eval swings)
                        if (i > 0) {
                            const evalDiff = Math.abs(evaluations[i] - evaluations[i-1]);
                            if (evalDiff > 200) { // Significant eval change
                                keyMoments.push({
                                    move: i,
                                    evalDiff: evalDiff,
                                    moveSan: move.san,
                                    position: tempGame.fen()
                                });
                            }
                        }
                    }
                    
                    // Create analysis HTML
                    let analysisHTML = '';
                    
                    // Create evaluation chart
                    analysisHTML += `
                        <div class="analysis-section">
                            <div class="analysis-section-title">Evaluation Graph</div>
                            <div class="analysis-chart-container">
                                <canvas id="analysisChart"></canvas>
                            </div>
                        </div>
                    `;
                    
                    // Create move analysis table
                    analysisHTML += `
                        <div class="analysis-section">
                            <div class="analysis-section-title">Move Analysis</div>
                            <table class="analysis-table">
                                <thead>
                                    <tr>
                                        <th>Move</th>
                                        <th>Evaluation</th>
                                        <th>Best Move</th>
                                    </tr>
                                </thead>
                                <tbody>
                    `;
                    
                    for (let i = 0; i < evaluations.length; i++) {
                        const evalText = evaluations[i] > 0 ? '+' + evaluations[i].toFixed(1) : evaluations[i].toFixed(1);
                        analysisHTML += `
                            <tr>
                                <td>${moveLabels[i]}</td>
                                <td>${evalText}</td>
                                <td>${bestMoves[i]}</td>
                            </tr>
                        `;
                    }
                    
                    analysisHTML += `
                                </tbody>
                            </table>
                        </div>
                    `;
                    
                    // Add key moments section
                    if (keyMoments.length > 0) {
                        analysisHTML += `
                            <div class="analysis-section">
                                <div class="analysis-section-title">Key Moments</div>
                                <div class="analysis-moves">
                        `;
                        
                        keyMoments.forEach((moment, idx) => {
                            analysisHTML += `
                                <div class="analysis-move" data-move="${moment.move}" data-fen="${moment.position}">
                                    Move ${moment.move}: ${moment.moveSan}<br>
                                    Eval change: ${moment.evalDiff > 0 ? '+' : ''}${moment.evalDiff.toFixed(1)}
                                </div>
                            `;
                        });
                        
                        analysisHTML += `
                                </div>
                            </div>
                        `;
                    }
                    
                    // Add opening information
                    analysisHTML += `
                        <div class="analysis-section">
                            <div class="analysis-section-title">Opening Information</div>
                            <div id="openingInfoContent">
                                ${this.getOpeningInfo()}
                            </div>
                        </div>
                    `;
                    
                    // Show analysis in modal
            // Update engine info display
            updateEngineInfoDisplay: function() {
                const info = this.currentEngineInfo;
                let infoText = "";
                
                if (info.depth) {
                    infoText += "Depth: " + info.depth;
                    if (info.seldepth) infoText += "/" + info.seldepth;
                    infoText += "\n";
                }
                
                if (info.score !== undefined) {
                    infoText += "Evaluation: ";
                    if (info.scoreType === 'mate') {
                        infoText += "Mate in " + Math.abs(info.score);
                        infoText += " (" + (info.score > 0 ? "White" : "Black") + " wins)";
                    } else {
                        infoText += (info.score > 0 ? "+" : "") + info.score.toFixed(2);
                        infoText += " (" + (info.score > 0 ? "White" : "Black") + " advantage)";
                    }
                    infoText += "\n";
                }
                
                if (info.time) {
                    infoText += "Time: " + info.time + "ms\n";
                }
                
                if (info.nodes) {
                    infoText += "Nodes: " + parseInt(info.nodes).toLocaleString() + "\n";
                }
                
                if (info.nps) {
                    infoText += "NPS: " + parseInt(info.nps).toLocaleString() + "\n";
                }
                
                if (info.pv) {
                    infoText += "PV: " + info.pv;
                }
                
            // Update engine info message
            updateEngineInfo: function(message) {
            // Handle engine move
            handleEngineMove: function(move) {
                if (!this.isEngineSolving) return;
                
                try {
                    this.logInfo("Engine plays: " + move);
                    const chessMove = this.game.move({
                        from: move.substring(0, 2),
                        to: move.substring(2, 4),
                        promotion: move.length > 4 ? move.substring(4, 5) : 'q'
                    }, { sloppy: true });
                    
                    if (chessMove) {
                        this.logInfo("Engine moved: " + chessMove.san);
                        this.addHighlights(chessMove);
                        this.board.position(this.game.fen());
                        this.updateMoveHistory();
                        this.updateMoveList();
                        
                            this.isEngineSolving = false;
                            this.gameOver(this.getGameResultMessage());
                            this.isEngineSolving = false;
                        } else if (this.isEngineSolving) {
                            // Continue solving for the selected side
                            setTimeout(() => {
                                const move = Sky5lEngine.get_best_move(this.game.fen(), parseInt(this.level));
                                if (move) this.handleEngineMove(move.from + move.to + (move.promotion || ''));
                            }, 500);
                        }
                    } else {
                        this.logInfo("Engine move invalid: " + move);
                        this.isEngineSolving = false;
                    this.logInfo("Error handling engine move: " + e);
                    this.isEngineSolving = false;
                    this.startEngineSolving("white");
                } else if (this.gameMode === "puzzle") {
                    // Start puzzle mode
                    this.loadRandomPuzzle();
                }
                
                // Update UI
                // Stop any engine analysis
                this.isEngineSolving = false;
            // Show engine settings modal
            showEngineSettingsModal: function() {
            // Apply engine settings
            applyEngineSettings: function() {
                this.updateEngineInfo("Engine settings updated");
            // Start engine solving for a side
            startEngineSolving: function(side) {
                if (this.game.game_over()) {
                    this.displayHint("Game is already over!");
                    return;
                }
                
                this.aiSolvingSide = side;
                    // Wait for the engine's turn, try again
                    setTimeout(() => this.startEngineSolving(side), 500);
                    return;
                }

                if ((side === "white" && this.game.turn() === "b") || 
                    (side === "black" && this.game.turn() === "w")) {
                    this.displayHint("It's not " + side + "'s turn to move!");
                    return;
                }
                
                this.isEngineSolving = true;
                this.updateEngineInfo("Engine calculating for " + side + "...");
                
                const move = Sky5lEngine.get_best_move(this.game.fen(), parseInt(this.level));
                if (move) this.handleEngineMove(move.from + move.to + (move.promotion || ''));
            },
            
            // Start new game
            startNewGame: function() {
                    if (!this.game.game_over() && !this.isEngineSolving) {
                        this.startClock();
                    }
                }
                
                // Check if game is over
                if (this.game.game_over()) {
                    this.gameOver(this.getGameResultMessage());
                    return;
                }
                
                if (!this.isEngineSolving && this.gameMode === "humanVsAI") {
                    this.stockfishMove();
                }
            },
            
            // Handle king of the hill move
            handleKingOfTheHillMove: function(move) {
                // In King of the Hill, the game is won by moving the king to the center
                const centerSquares = ['e4', 'e5', 'd4', 'd5'];
                if (move.piece === 'k' && centerSquares.includes(move.to)) {
                    this.gameOver((move.color === 'w' ? "White" : "Black") + " wins by King of the Hill!");
                }
            },
            
            // Handle three-check move
            handleThreeCheckMove: function(move) {
                // In Three-check, the game is won by giving check three times
                // This would require tracking checks, which isn't implemented in chess.js
                // You would need to extend the game state to track this
            },
            
            // Update move history
            updateMoveHistory: function() {
                // If we're not at the end of history, truncate the future moves
                if (this.currentMoveIndex < this.moveHistory.length - 1) {
                    this.moveHistory = this.moveHistory.slice(0, this.currentMoveIndex + 1);
                }
                
                // Add new position to history
                this.moveHistory.push(this.game.fen());
                this.currentMoveIndex++;
                
                // Update button states
                const move = Sky5lEngine.get_best_move(this.game.fen(), parseInt(this.level));
                if (move) this.handleEngineMove(move.from + move.to + (move.promotion || ''));
            },
            
            // Show hint
            showHint: function() {
                if (this.game.game_over()) {
                    this.displayHint("Game is already over!");
                    return;
                }
                
                if (this.game.turn() !== (this.userColor === "white" ? 'w' : 'b')) {
                    this.displayHint("Wait for your turn!");
                    return;
                }
                
                // Clear previous hints
                this.$board.find(".square-55d63").removeClass("hint-move");
                
                this.displayHint("Calculating best move...");
                
                this.isHintActive = true;
                this.requestBestMove(3);
            },
            
            // Export PGN
            exportPGN: function() {
                if (this.game.history().length === 0) {
                    this.displayHint("No game to export.");
                    return;
                }

                try {
                    // Create PGN with properly formatted headers
                    const headers = {
                        Event: "SKY5LChess Game",
                        Site: "Local",
                        Date: new Date().toISOString().split('T')[0].replace(/-/g, "."),
                        Round: "1",
                        White: "Player",
                        Black: "Player",
                        Result: this.getGameResult(),
                        Variant: this.gameVariant,
                        TimeControl: this.currentClockType,
                        FEN: this.moveHistory[0] // Include starting position
                    };
                    
                    // Set the headers
                    this.game.header(headers);
                    
                    // Get the PGN with proper formatting
                    let pgn = this.game.pgn({
                        newline_char: '\r\n',  // Windows-style line endings
                        max_width: 80          // Standard PGN line width
                    });
                    
                    // Ensure proper header formatting
                    pgn = pgn.replace(/\]\s*\[/g, "]\n[");
                    
                    // Create download link
                    const blob = new Blob([pgn], { type: "text/plain;charset=utf-8" });
                    const url = URL.createObjectURL(blob);
                    const a = document.createElement("a");
                    a.href = url;
                    a.download = `chess_game_${headers.Date.replace(/\./g, "-")}_${headers.Result.replace(/\//g, "-")}.pgn`;
                    document.body.appendChild(a);
                    a.click();
                    
                    // Clean up
                    setTimeout(() => {
                        document.body.removeChild(a);
                        window.URL.revokeObjectURL(url);
                    }, 100);
                    
                    this.displayHint("PGN exported successfully");
                    this.hidePgnOptions();
                } catch (e) {
                    console.error("Export failed:", e);
                    this.displayHint("Export failed: " + e.message);
                }
            },
            
            // Import PGN
            importPGN: function() {
                this.isEngineSolving = false;
                this.isHintActive = false;
                this.puzzleMode = false;
                this.currentPuzzle = null;
                this.userMoves = [];
                this.stopClock();
            },
            
            updateUIAfterImport: function() {
        // Enhanced Sunfish chess engine implementation
        const Sky5lEngine = {
            // Piece values
            pieceValues: { p: 100, n: 320, b: 330, r: 500, q: 900, k: 20000 },
            
            // Piece-square tables
            pst: {
                p: [
                    0,   0,   0,   0,   0,   0,   0,   0,
                    78,  83,  86,  73, 102,  82,  85,  90,
                    7,  29,  21,  44,  40,  31,  44,   7,
                    -17,  16,  -2,  15,  14,   0,  15, -13,
                    -26,   3,  10,   9,   6,   1,   0, -23,
                    -22,   9,   5, -11, -10,  -2,   3, -19,
                    -31,   8,  -7, -37, -36, -14,   3, -31,
                    0,   0,   0,   0,   0,   0,   0,   0
                ],
                n: [
                    -66, -53, -75, -75, -10, -55, -58, -70,
                    -3,  -6, 100, -36,   4,  62,  -4, -14,
                    10,  67,   1,  74,  73,  27,  62,  -2,
                    24,  24,  45,  37,  33,  41,  25,  17,
                    -1,   5,  31,  21,  22,  35,   2,   0,
                    -18,  10,  13,  22,  18,  15,  11, -14,
                    -23, -15,   2,   0,   2,   0, -23, -20,
                    -74, -23, -26, -24, -19, -35, -22, -69
                ],
                b: [
                    -59, -78, -82, -76, -23,-107, -37, -50,
                    -11,  20,  35, -42, -39,  31,   2, -22,
                    -9,  39, -32,  41,  52, -10,  28, -14,
                    25,  17,  20,  34,  26,  25,  15,  10,
                    13,  10,  17,  23,  17,  16,   0,   7,
                    14,  25,  24,  15,   8,  25,  20,  15,
                    19,  20,  11,   6,   7,  6,  20,  16,
                    -7,   2, -15, -12, -14, -15, -10, -10
                ],
                r: [
                    35,  29,  33,   4,  37,  33,  56,  50,
                    55,  29,  56,  67,  55,  62,  34,  60,
                    19,  35,  28,  33,  45,  27,  25,  15,
                    0,   5,  16,  13,  18,  -4,  -9,  -6,
                    -28, -35, -16, -21, -13, -29, -46, -30,
                    -42, -28, -42, -25, -25, -35, -26, -46,
                    -53, -38, -31, -26, -29, -43, -44, -53,
                    -30, -24, -18,   5,  -2, -18, -31, -32
                ],
                q: [
                    6,   1,  -8,-104,  69,  24,  88,  26,
                    14,  32,  60, -10,  20,  76,  57,  24,
                    -2,  43,  32,  60,  72,  63,  43,   2,
                    1, -16,  22,  17,  25,  20, -13,  -6,
                    -14, -15,  -2,  -5,  -1, -10, -20, -22,
                    -30,  -6, -13, -11, -16, -11, -16, -27,
                    -36, -18,   0, -19, -15, -15, -21, -38,
                    -39, -30, -31, -13, -31, -36, -34, -42
                ],
                k: [
                    4,  54,  47, -99, -99,  60,  83, -62,
                    -32,  10,  55,  56,  56,  55,  10,   3,
                    -62,  12, -57,  44, -67,  28,  37, -31,
                    -55,  50,  11,  -4, -19,  13,   0, -49,
                    -55, -43, -52, -28, -51, -47,  -8, -50,
                    -47, -42, -43, -79, -64, -32, -29, -32,
                    -4,   3, -14, -50, -57, -18,  13,   4,
                    17,  30,  -3, -14,   6,  -1,  40,  18
                ]
            },
            
            // Evaluation parameters
            params: {
                tempo: 10,
                mobility: 1,
                pawnStructure: 1,
                kingSafety: 1
            },
            
            // Transposition table
            transpositionTable: {},
            
            // Convert square to index
            squareToIndex: function(square) {
                const file = square.charCodeAt(0) - 'a'.charCodeAt(0);
                const rank = parseInt(square[1]) - 1;
                return rank * 8 + file;
            },
            
            // Evaluate position with additional terms
            evaluate: function(game) {
                let score = 0;
                const board = game.board();
                
                // Material and piece-square tables
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece) {
                            const value = this.pieceValues[piece.type];
                            const pstValue = this.pst[piece.type][piece.color === 'w' ? 
                                (7 - i) * 8 + j : i * 8 + j];
                            
                            score += piece.color === 'w' ? value + pstValue : -(value + pstValue);
                        }
                    }
                }
                
                // Tempo bonus
                score += game.turn() === 'w' ? this.params.tempo : -this.params.tempo;
                
                // Mobility - number of legal moves
                const mobility = game.moves().length;
                score += game.turn() === 'w' ? mobility * this.params.mobility : -mobility * this.params.mobility;
                
                // Pawn structure evaluation
                score += this.evaluatePawnStructure(game);
                
                // King safety
                score += this.evaluateKingSafety(game);
                
                return Math.round(score * 10) / 10; // Round to 1 decimal place
            },
            
            // Evaluate pawn structure
            evaluatePawnStructure: function(game) {
                let score = 0;
                const board = game.board();
                
                // Count doubled, isolated, and passed pawns
                const whitePawns = { files: {}, ranks: {} };
                const blackPawns = { files: {}, ranks: {} };
                
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece && piece.type === 'p') {
                            const file = String.fromCharCode(97 + j);
                            const rank = 8 - i;
                            
                            if (piece.color === 'w') {
                                whitePawns.files[file] = (whitePawns.files[file] || 0) + 1;
                                whitePawns.ranks[rank] = (whitePawns.ranks[rank] || 0) + 1;
                            } else {
                                blackPawns.files[file] = (blackPawns.files[file] || 0) + 1;
                                blackPawns.ranks[rank] = (blackPawns.ranks[rank] || 0) + 1;
                            }
                        }
                    }
                }
                
                // Penalize doubled pawns
                for (const file in whitePawns.files) {
                    if (whitePawns.files[file] > 1) {
                        score -= 20 * (whitePawns.files[file] - 1);
                    }
                }
                
                for (const file in blackPawns.files) {
                    if (blackPawns.files[file] > 1) {
                        score += 20 * (blackPawns.files[file] - 1);
                    }
                }
                
                // TODO: Add more sophisticated pawn structure evaluation
                
                return score;
            },
            
            // Evaluate king safety
            evaluateKingSafety: function(game) {
                let score = 0;
                const board = game.board();
                
                // Find kings
                let whiteKingPos = null;
                let blackKingPos = null;
                
                for (let i = 0; i < 8; i++) {
                    for (let j = 0; j < 8; j++) {
                        const piece = board[i][j];
                        if (piece && piece.type === 'k') {
                            if (piece.color === 'w') {
                                whiteKingPos = { x: j, y: i };
                            } else {
                                blackKingPos = { x: j, y: i };
                            }
                        }
                    }
                }
                
                // Penalize early queen moves near king
                // TODO: Add more sophisticated king safety evaluation
                
                return score;
            },
            
            // Generate all legal moves with improved move ordering
            generateMoves: function(game) {
                const moves = game.moves({verbose: true});
                
                // Improved move ordering:
                // 1. Captures (MVV/LVA - Most Valuable Victim / Least Valuable Attacker)
                // 2. Promotions
                // 3. Killer moves (from history)
                // 4. Quiet moves
                
                                moves.sort((a, b) => {
                    // Prioritize captures
                    if (a.captured && !b.captured) return -1;
                    if (!a.captured && b.captured) return 1;
                    
                    if (a.captured && b.captured) {
                        // MVV/LVA - capture highest value piece with lowest value attacker
                        const aValue = this.pieceValues[a.captured] - this.pieceValues[a.piece];
                        const bValue = this.pieceValues[b.captured] - this.pieceValues[b.piece];
                        return bValue - aValue;
                    }
                    
                    // Then prioritize promotions
                    if (a.promotion && !b.promotion) return -1;
                    if (!a.promotion && b.promotion) return 1;
                    
                    // Then prioritize checks
                    if (a.san.includes('+') && !b.san.includes('+')) return -1;
                    if (!a.san.includes('+') && b.san.includes('+')) return 1;
                    
                    return 0;
                });
                
                return moves;
            },
            
            // Search for best move using minimax with alpha-beta pruning and transposition table
            search: function(game, depth, alpha, beta, maximizingPlayer, ply = 0) {
                // Check transposition table first
                const fen = game.fen();
                const ttEntry = this.transpositionTable[fen];
                
                if (ttEntry && ttEntry.depth >= depth) {
                    if (ttEntry.flag === 'exact') {
                        return { score: ttEntry.score, move: ttEntry.move };
                    } else if (ttEntry.flag === 'lowerbound') {
                        alpha = Math.max(alpha, ttEntry.score);
                    } else if (ttEntry.flag === 'upperbound') {
                        beta = Math.min(beta, ttEntry.score);
                    }
                    
                    if (alpha >= beta) {
                        return { score: ttEntry.score, move: ttEntry.move };
                    }
                }
                
                if (depth === 0 || game.game_over()) {
                    return { score: this.evaluate(game) };
                }
                
                const moves = this.generateMoves(game);
                if (moves.length === 0) {
                    return { score: this.evaluate(game) };
                }
                
                let bestMove = null;
                let bestScore = maximizingPlayer ? -Infinity : Infinity;
                let flag = 'exact';
                
                for (const move of moves) {
                    game.move(move);
                    
                    const result = this.search(game, depth - 1, alpha, beta, !maximizingPlayer, ply + 1);
                    game.undo();
                    
                    if (maximizingPlayer) {
                        if (result.score > bestScore) {
                            bestScore = result.score;
                            bestMove = move;
                            
                            if (bestScore > alpha) {
                                alpha = bestScore;
                                flag = 'exact';
                            }
                            
                            if (alpha >= beta) {
                                flag = 'lowerbound';
                                break; // Beta cutoff
                            }
                        }
                    } else {
                        if (result.score < bestScore) {
                            bestScore = result.score;
                            bestMove = move;
                            
                            if (bestScore < beta) {
                                beta = bestScore;
                                flag = 'exact';
                            }
                            
                            if (alpha >= beta) {
                                flag = 'upperbound';
                                break; // Alpha cutoff
                            }
                        }
                    }
                }
                
                // Store result in transposition table
                this.transpositionTable[fen] = {
                    depth: depth,
                    score: bestScore,
                    move: bestMove,
                    flag: flag
                };
                
                return { move: bestMove, score: bestScore };
            },
            
            // Quiescence search to avoid horizon effect
            quiesce: function(game, alpha, beta, maximizingPlayer) {
                const standPat = this.evaluate(game);
                
                if (maximizingPlayer) {
                    if (standPat >= beta) return beta;
                    alpha = Math.max(alpha, standPat);
                } else {
                    if (standPat <= alpha) return alpha;
                    beta = Math.min(beta, standPat);
                }
                
                const moves = game.moves({verbose: true}).filter(m => m.captured);
                
                for (const move of moves) {
                    game.move(move);
                    const score = this.quiesce(game, alpha, beta, !maximizingPlayer);
                    game.undo();
                    
                    if (maximizingPlayer) {
                        if (score >= beta) return beta;
                        alpha = Math.max(alpha, score);
                    } else {
                        if (score <= alpha) return alpha;
                        beta = Math.min(beta, score);
                    }
                }
                
                return maximizingPlayer ? alpha : beta;
            },
            
            // Get best move with iterative deepening and time management
            get_best_move: function(fen, depth = 3) {
                const game = new Chess(fen);
                const moves = game.moves({verbose: true});
                
                if (moves.length === 0) return null;
                
                // If only one move available, return it immediately
                if (moves.length === 1) return moves[0];
                
                // Clear transposition table for new search
                this.transpositionTable = {};
                
                // Use iterative deepening for better move selection
                let bestMove = null;
                let bestScore = game.turn() === 'w' ? -Infinity : Infinity;
                const startTime = Date.now();
                const maxTime = 5000; // Max 5 seconds per move
                
                for (let currentDepth = 1; currentDepth <= depth; currentDepth++) {
                    const result = this.search(game, currentDepth, -Infinity, Infinity, game.turn() === 'w');
                    
                    if (result.move) {
                        bestMove = result.move;
                        bestScore = result.score;
                    }
                    
                    // If we found a checkmate, no need to search deeper
                    if (Math.abs(bestScore) > 10000) break;
                    
                    // Check time elapsed
                    if (Date.now() - startTime > maxTime) break;
                }
                
                return bestMove || moves[Math.floor(Math.random() * moves.length)];
            }
        };

        // Initialize the game when the document is ready

// === Event Listeners ===
            $board: $('#myBoard'),
            isPlaying: false,
            playInterval: null,
                window.addEventListener('beforeunload', () => this.destroy());
            },
            
            // Clean up resources
            destroy: function() {
                if (this.clockInterval) {
                    clearInterval(this.clockInterval);
                }
                if (this.playInterval) {
                    clearInterval(this.playInterval);
                }
                if (this.analysisChart) {
                    this.analysisChart.destroy();
                }
            },
            
            // Create arrow layer for hints and analysis
            createArrowLayer: function() {
                const arrowLayer = document.createElement("canvas");
                arrowLayer.id = "arrowLayer";
                $('#databaseTable').bootstrapTable({
                    search: true,
                    showSearchClearButton: true,
                    filterControl: true,
                    columns: [{
                        field: 'state',
                        checkbox: true,
                        visible: true
                    }, {
                        field: 'white',
                        title: 'White',
                        filterControl: 'input',
                        sortable: true
                    }, {
                        field: 'black',
                        title: 'Black',
                        filterControl: 'input',
                        sortable: true
                    }, {
                        field: 'result',
                        title: 'Result',
                        filterControl: 'select',
                        sortable: true
                    }, {
                        field: 'event',
                        title: 'Event',
                        filterControl: 'input',
                        sortable: true
                    }, {
                        field: 'date',
                        title: 'Date',
                        sortable: true
                    }],
                    pagination: true,
                    pageSize: 5,
                    pageList: [5, 10, 20],
                    clickToSelect: true,
                    singleSelect: true
                });
            },
            
            // Setup all event handlers with consistent binding
            setupEventHandlers: function() {
                // Button click handlers
                $("#editBtn").click(() => this.toggleEditMode());
                $("#startBtn").click(() => this.showNewGameModal());
                $("#goBackBtn").click(() => this.stepBack());
                $("#goForwardBtn").click(() => this.stepForward());
                $("#flipOrientationBtn").click(() => this.flipBoard());
                $("#pgnBtn").click(() => this.togglePgnOptions());
                $("#exportPgnBtn").click(() => this.exportPGN());
                $("#importSinglePgnBtn").click(() => this.showImportOptions(false));
                $("#importMultiPgnBtn").click(() => this.handleMultiPgnImport());
                $("#cancelPgnBtn").click(() => this.hidePgnOptions());
                $("#playPauseBtn").click(() => this.togglePlayPause());
                $("#engineSolveBtn").click(() => this.showAiSideModal());
                $("#hintBtn").click(() => this.showHint());
                $("#loadPgnBtn").click(() => this.importPGN());
                $("#cancelImportBtn").click(() => this.hidePgnInput());
                $("#loadDatabaseBtn").click(() => this.loadSelectedDatabaseGame());
                $("#cancelDatabaseBtn").click(() => this.hideDatabaseSelector());
                $("#pgnFileInput").change((e) => this.handleFileImport(e));
                $("#aiWhiteBtn").click(() => this.startEngineSolving("white"));
                $("#aiBlackBtn").click(() => this.startEngineSolving("black"));
                $("#aiCancelBtn").click(() => $("#aiSideModal").hide());
                $("#signinBtn").click(() => this.showLoginModal());
                $("#loginSubmitBtn").click(() => this.handleLogin());
                $("#registerBtn").click(() => this.handleRegister());
                $("#loginModal .modal-content").click((e) => e.stopPropagation());
                $("#loginModal").click(() => this.hideLoginModal());
                $("#newGameStartBtn").click(() => this.startNewGameWithSettings());
                $("#newGameCancelBtn").click(() => $("#newGameModal").hide());
                $("#engineSettingsBtn").click(() => this.showEngineSettingsModal());
                $("#engineSettingsApplyBtn").click(() => this.applyEngineSettings());
                $("#engineSettingsCancelBtn").click(() => $("#engineSettingsModal").hide());
                $("#engineSelect").change(() => {
                    if ($("#engineSelect").val() === "custom") {
                        $("#customEngineGroup").show();
                    } else {
                        $("#customEngineGroup").hide();
                    }
                });
                $("#togglePanelBtn").click(() => this.togglePanel());
                $("#panelHeader").click(() => this.togglePanel());
                $("#puzzleBtn").click(() => this.loadRandomPuzzle());
                $("#analysisBtn").click(() => this.analyzeGameMoves());
                $("#closeAnalysisBtn").click(() => {
                    $("#analysisModal").hide();
                    if (this.analysisChart) {
                        this.analysisChart.destroy();
                        this.analysisChart = null;
                    }
                });
                $("#clockSelect").change(() => {
                    if ($("#clockSelect").val() === "custom") {
                        $("#customTimeGroup").show();
                    } else {
                        $("#customTimeGroup").hide();
                    }
                });
                
                // Theme selector handlers
                $(".theme-btn").click((e) => {
                    $(".theme-btn").removeClass("selected");
                    $(e.currentTarget).addClass("selected");
                    this.currentTheme = $(e.currentTarget).data("theme");
                    this.applyTheme(this.currentTheme);
                });
                
                // Piece theme selector handlers
                $(".piece-theme-btn").click((e) => {
                    $(".piece-theme-btn").removeClass("selected");
                    $(e.currentTarget).addClass("selected");
                    this.currentPieceTheme = $(e.currentTarget).data("piece-theme");
                    this.board.position(this.game.fen()); // Redraw board with new pieces
                });
            },
            
            // Apply selected theme
            applyTheme: function(theme) {
                this.currentTheme = theme;
                const root = document.documentElement;
                
                switch(theme) {
                    case "blue":
                        root.style.setProperty('--dark-tile', '#5d8aa8');
                        root.style.setProperty('--light-tile', '#e6e6fa');
                        root.style.setProperty('--dark-tile-highlight', '#7d9ec0');
                        root.style.setProperty('--light-tile-highlight', '#f0f8ff');
                        break;
                    case "green":
                        root.style.setProperty('--dark-tile', '#556b2f');
                        root.style.setProperty('--light-tile', '#f5fffa');
                        root.style.setProperty('--dark-tile-highlight', '#6b8e23');
                        root.style.setProperty('--light-tile-highlight', '#f0fff0');
                        break;
                    case "dark":
                        root.style.setProperty('--dark-tile', '#333');
                        root.style.setProperty('--light-tile', '#666');
                        root.style.setProperty('--dark-tile-highlight', '#555');
                        root.style.setProperty('--light-tile-highlight', '#888');
                        break;
                    default: // default
                        root.style.setProperty('--dark-tile', '#6E470B');
                        root.style.setProperty('--light-tile', '#f8e7bb');
                        root.style.setProperty('--dark-tile-highlight', '#bbc34a');
                        root.style.setProperty('--light-tile-highlight', '#f6f668');
                }
                
                // Redraw board to apply theme changes
                if (this.board) {
                    this.board.position(this.game.fen());
                }
            },
            
            // Load opening book data
            loadOpeningBook: function() {
                // This would be replaced with actual opening book data
                // For now, we'll use a small sample
                this.openingBook = {
                    "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR": {
                        "e2e4": { name: "King's Pawn Opening", frequency: 1000 },
                        "d2d4": { name: "Queen's Pawn Opening", frequency: 800 },
                        "c2c4": { name: "English Opening", frequency: 300 },
                        "g1f3": { name: "Reti Opening", frequency: 200 }
                    },
                    "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR": {
                        "e7e5": { name: "Open Game", frequency: 800 },
                        "c7c5": { name: "Sicilian Defense", frequency: 700 },
                        "e7e6": { name: "French Defense", frequency: 300 },
                        "c7c6": { name: "Caro-Kann Defense", frequency: 250 }
                    }
                };
            },
            
            // Show loading overlay
            showLoading: function() {
                $("#loadingOverlay").show();
            },
            
            // Hide loading overlay
            hideLoading: function() {
                $("#loadingOverlay").hide();
            },
            
            // Handle multi-PGN import
            handleMultiPgnImport: function() {
                this.showImportOptions(true);
            },
            
            // Handle file import
            handleFileImport: function(event) {
                const files = event.target.files;
                if (files.length === 0) return;

                const games = [];
                let filesProcessed = 0;

                Array.from(files).forEach((file) => {
                    const reader = new FileReader();
                    reader.onload = (e) => {
                        const content = e.target.result;
                        const gameSections = content.split(/\n\s*\n(?=\[Event )/);
                        
                        gameSections.forEach((pgn) => {
                            pgn = pgn.trim();
                            if (!pgn) return;
                            
                            try {
                                $('#databaseTable').bootstrapTable('load', games);
                                $('#databaseSelector').show();
                            } else {
                                alert("No valid games found in the PGN files");
                            }
                        }
                    };
                    reader.readAsText(file);
                });
            },
            
            // Load selected database game
            loadSelectedDatabaseGame: function() {
                const selections = $('#databaseTable').bootstrapTable('getSelections');
                if (selections.length === 0) {
                    this.displayHint("Please select a game first");
                    return;
                }
                
                const selectedGame = selections[0];
                try {
                    this.processPGNImport(selectedGame.pgn);
                    this.displayHint(`Loaded game: ${selectedGame.white} vs ${selectedGame.black}`);
                    this.hideDatabaseSelector();
                } catch (e) {
                    this.displayHint("Error loading game: " + e.message);
                }
            },
            
            // Update database list
            updateDatabaseList: function() {
                $('#databaseTable').bootstrapTable('load', this.databaseGames);
            },
            
            // Position validation system
            isValidPosition: function() {
                const kings = this.countKings();
                
                // Variant-specific checks
                switch(this.gameVariant) {
                const $explosion = $('<div>').addClass('atomic-explosion');
                this.$board.append($explosion);
                setTimeout(() => $explosion.remove(), 1000);

                // Explode surrounding pieces
                const directions = [{x:-1,y:-1},{x:0,y:-1},{x:1,y:-1},{x:-1,y:0},{x:1,y:0},{x:-1,y:1},{x:0,y:1},{x:1,y:1}];
                const [file, rank] = [move.to.charCodeAt(0)-97, parseInt(move.to[1])];
                
                directions.forEach(dir => {
                    const newFile = file + dir.x;
                    const newRank = rank + dir.y;
                    if (newFile >= 0 && newFile < 8 && newRank >= 1 && newRank <= 8) {
                        const square = String.fromCharCode(97+newFile) + newRank;
                        const piece = this.game.get(square);
                        if (piece && piece.type !== 'p') this.game.remove(square);
                    }
                });

                // Check if kings were exploded
                const kings = this.getKingPositions();
                if (!this.game.get(kings.white)) {
                    this.gameOver("Black wins by atomic explosion!");
                } else if (!this.game.get(kings.black)) {
                    this.gameOver("White wins by atomic explosion!");
                }
            },
            

            
            
                if (!$("#puzzleIndicator").length) {
                    const $indicator = $('<div class="puzzle-indicator">Puzzle Mode</div>');
                    $(".board-container").append($indicator);
                }
            },
            
            // Analyze game moves with improved evaluation
            analyzeGameMoves: function() {
                if (this.game.history().length === 0) {
                    this.displayHint("No moves to analyze");
                    return;
                }

                this.showLoading();
                this.displayHint("Analyzing game...");
                
                setTimeout(() => {
                    // Create a temporary game to replay moves
                    $("#analysisContent").html(analysisHTML);
                    
                    // Initialize chart
                    this.createEvaluationChart(evaluations, moveLabels);
                    
                    // Set up click handlers for key moments
                    $(".analysis-move").click((e) => {
                        const moveIndex = $(e.currentTarget).data("move");
                        const fen = $(e.currentTarget).data("fen");
                        this.game.load(fen);
                        this.board.position(fen);
                        $(".analysis-move").removeClass("active");
                        $(e.currentTarget).addClass("active");
                    });
                    
                    $("#analysisModal").show();
                    this.hideLoading();
                }, 50);
            },
            
            // Get opening information for current game
            getOpeningInfo: function() {
                $("#engineInfoContent").text(infoText || "No engine information available");
            },
            
                $("#engineInfoContent").text(message);
            },
            
            // Display hint text
            displayHint: function(text) {
                $("#hintText").text(text);
                $("#hintContainer").show();
                setTimeout(() => {
                    $("#hintContainer").fadeOut(2000);
                }, 5000);
            },
            
                        if ($("#playPauseBtn").prop("disabled")) {
                            $("#playPauseBtn").prop("disabled", false);
                        }
                        
                        // Check if game is over
                        if (this.game.game_over()) {
                            $("#engineSolveBtn").prop("disabled", false).html('<i class="fas fa-robot"></i> <span>Engine</span>');
                            return;
                        }
                        
                        // Check if we should continue solving
                        if ((this.aiSolvingSide === "white" && this.game.turn() === "b") || 
                            (this.aiSolvingSide === "black" && this.game.turn() === "w")) {
                            // It's the other side's turn, stop solving
                            $("#engineSolveBtn").prop("disabled", false).html('<i class="fas fa-robot"></i> <span>Engine</span>');
                        $("#engineSolveBtn").prop("disabled", false).html('<i class="fas fa-robot"></i> <span>Engine</span>');
                    }
                } catch (e) {
                    $("#engineSolveBtn").prop("disabled", false).html('<i class="fas fa-robot"></i> <span>Engine</span>');
                }
            },
            
            // Show hint move
            showHintMove: function(move) {
                // Clear previous hints
                this.$board.find(".square-55d63").removeClass("hint-move");
                
                // Get the from and to squares from the move
                const from = move.substring(0, 2);
                const to = move.substring(2, 4);
                
                // Highlight the suggested move
                this.$board.find(".square-" + from).addClass("hint-move");
                this.$board.find(".square-" + to).addClass("hint-move");
                
                // Draw arrow for the move
                this.drawArrow(from, to, "rgba(0,255,0,0.6)");
                
                // Try to get the SAN notation for the move
                const tempGame = new Chess(this.game.fen());
                const tempMove = tempGame.move({
                    from: from,
                    to: to,
                    promotion: move.length > 4 ? move.substring(4, 5) : 'q'
                });
                
                if (tempMove) {
                    this.displayHint("Best move: " + tempMove.san);
                } else {
                    this.displayHint("Best move: " + move);
                }
            },
            
            // Toggle edit mode
            toggleEditMode: function() {
                this.isEditing = !this.isEditing;
                
                if (this.isEditing) {
                    this.board = Chessboard('myBoard', this.configs.edit);
                    $("#editBtn").html('<i class="fas fa-check"></i> <span>Done Editing</span>');
                    $("#startBtn").prop("disabled", true);
                    $("#goBackBtn").prop("disabled", true);
                    $("#goForwardBtn").prop("disabled", true);
                    $("#playPauseBtn").prop("disabled", true);
                    $("#engineSolveBtn").prop("disabled", true);
                    $("#hintBtn").prop("disabled", true);
                } else {
                    this.board = Chessboard('myBoard', this.configs.start);
                    $("#editBtn").html('<i class="fas fa-edit"></i> <span>Edit Board</span>');
                    $("#startBtn").prop("disabled", false);
                    $("#goBackBtn").prop("disabled", false);
                    $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
                    $("#playPauseBtn").prop("disabled", this.game.history().length === 0);
                    $("#engineSolveBtn").prop("disabled", false);
                    $("#hintBtn").prop("disabled", false);
                }
            },
            
            // Show new game modal
            showNewGameModal: function() {
                $("#newGameModal").show();
            },
            
            // Start new game with settings
            startNewGameWithSettings: function() {
                this.gameMode = $("#gameModeSelect").val();
                this.gameVariant = $("#gameVariantSelect").val();
                this.currentClockType = $("#clockSelect").val();
                
                // Set clock time
                if (this.currentClockType === "custom") {
                    const minutes = parseInt($("#customTimeInput").val()) || 10;
                    this.whiteTime = minutes * 60;
                    this.blackTime = minutes * 60;
                } else {
                    switch(this.currentClockType) {
                        case "bullet":
                            this.whiteTime = 60;
                            this.blackTime = 60;
                            break;
                        case "blitz":
                            this.whiteTime = 300;
                            this.blackTime = 300;
                            break;
                        case "rapid":
                            this.whiteTime = 600;
                            this.blackTime = 600;
                            break;
                        case "classical":
                            this.whiteTime = 1800;
                            this.blackTime = 1800;
                            break;
                        case "none":
                        default:
                            this.whiteTime = 0;
                            this.blackTime = 0;
                    }
                }
                
                // Initialize game based on variant
                switch(this.gameVariant) {
                    case "standard":
                $("#playPauseBtn").prop("disabled", true).html('<i class="fas fa-play"></i> <span>Play</span>');
                $("#goBackBtn").prop("disabled", true);
                $("#goForwardBtn").prop("disabled", true);
                $("#hintContainer").hide();
                this.$board.find(".square-55d63").removeClass("hint-move");
                this.updateMoveList();
                
                $("#newGameModal").hide();
            },
            
            // Generate Chess960 position
            generateChess960Position: function() {
                let pieces = ['r', 'n', 'b', 'q', 'k', 'b', 'n', 'r'];
                
                // Fisher-Yates shuffle
                for (let i = pieces.length - 1; i > 0; i--) {
                    const j = Math.floor(Math.random() * (i + 1));
                    [pieces[i], pieces[j]] = [pieces[j], pieces[i]];
                }
                
                // Ensure bishops are on opposite colors
                while (true) {
                    let bishop1 = pieces.indexOf('b');
                    let bishop2 = pieces.indexOf('b', bishop1 + 1);
                    
                    if ((bishop1 % 2) !== (bishop2 % 2)) break;
                    
                    // If bishops are on same color, shuffle again
                    for (let i = pieces.length - 1; i > 0; i--) {
                        const j = Math.floor(Math.random() * (i + 1));
                        [pieces[i], pieces[j]] = [pieces[j], pieces[i]];
                    }
                }
                
                // Ensure king is between rooks
                while (true) {
                    let rook1 = pieces.indexOf('r');
                    let king = pieces.indexOf('k');
                    let rook2 = pieces.indexOf('r', rook1 + 1);
                    
                    if (rook1 < king && king < rook2) break;
                    
                    // If king is not between rooks, shuffle again
                    for (let i = pieces.length - 1; i > 0; i--) {
                        const j = Math.floor(Math.random() * (i + 1));
                        [pieces[i], pieces[j]] = [pieces[j], pieces[i]];
                    }
                }
                
                // Create FEN string
                const fen = pieces.join('') + '/pppppppp/8/8/8/8/PPPPPPPP/' + 
                         pieces.join('').toUpperCase() + ' w KQkq - 0 1';
                
                return fen;
            },
            
            // Setup clock
            setupClock: function() {
                // Clear any existing clock
                if (this.clockInterval) {
                    clearInterval(this.clockInterval);
                    this.clockInterval = null;
                }
                
                // Update clock display
                this.updateClockDisplay();
                
                if (this.currentClockType === "none") {
                    $("#clockContainer").hide();
                    return;
                }
                
                $("#clockContainer").show();
                
                // Start clock if it's a human's turn
                if (this.gameMode === "humanVsHuman" || 
                    (this.gameMode === "humanVsAI" && this.game.turn() === (this.userColor === "white" ? 'w' : 'b'))) {
                    this.startClock();
                }
            },
            
            // Start clock
            startClock: function() {
                if (this.clockInterval) clearInterval(this.clockInterval);
                
                // Highlight active clock
                $(".clock").removeClass("active");
                if (this.game.turn() === 'w') {
                    $("#whiteClock").addClass("active");
                } else {
                    $("#blackClock").addClass("active");
                }
                
                this.clockInterval = setInterval(() => {
                    if (this.game.turn() === 'w') {
                        this.whiteTime--;
                        if (this.whiteTime <= 0) {
                            this.whiteTime = 0;
                            this.gameOver("Black wins on time");
                        }
                    } else {
                        this.blackTime--;
                        if (this.blackTime <= 0) {
                            this.blackTime = 0;
                            this.gameOver("White wins on time");
                        }
                    }
                    
                    this.updateClockDisplay();
                    
                    // Flash clock when time is low
                    if ((this.game.turn() === 'w' && this.whiteTime <= 10) || 
                        (this.game.turn() === 'b' && this.blackTime <= 10)) {
                        $(".clock").removeClass("low-time");
                        if (this.game.turn() === 'w') {
                            $("#whiteClock").addClass("low-time");
                        } else {
                            $("#blackClock").addClass("low-time");
                        }
                    }
                }, 1000);
            },
            
            // Stop clock
            stopClock: function() {
                if (this.clockInterval) {
                    clearInterval(this.clockInterval);
                    this.clockInterval = null;
                }
                $(".clock").removeClass("active low-time");
            },
            
            // Update clock display
            updateClockDisplay: function() {
                $("#whiteClock").text(formatTime(this.whiteTime));
                $("#blackClock").text(formatTime(this.blackTime));
            },
            
            // Get game result message
            getGameResultMessage: function() {
                if (this.game.in_checkmate()) {
                    return this.game.turn() === 'w' ? "Black wins by checkmate" : "White wins by checkmate";
                }
                if (this.game.in_draw()) {
                    if (this.game.in_stalemate()) return "Game drawn by stalemate";
                    if (this.game.in_threefold_repetition()) return "Game drawn by threefold repetition";
                    if (this.game.insufficient_material()) return "Game drawn by insufficient material";
                    return "Game drawn";
                }
                return "Game over";
            },
            
            // Game over handler
            gameOver: function(message) {
                this.stopClock();
                this.displayHint(message);
                this.logInfo(message);
                
                $("#engineSolveBtn").prop("disabled", false).html('<i class="fas fa-robot"></i> <span>Engine</span>');
            },
            
                $("#engineSettingsModal").show();
            },
            
                this.currentEngine = $("#engineSelect").val();
                this.level = $("#skillLevelSelect").val();
                $("#engineSettingsModal").hide();
            },
            
            // Toggle side panel
            togglePanel: function() {
                this.panelVisible = !this.panelVisible;
                if (this.panelVisible) {
                    $("#sidePanel").show();
                    $("#panelContent").slideDown();
                    $("#panelToggleIcon").removeClass("fa-chevron-down").addClass("fa-chevron-up");
                } else {
                    $("#panelContent").slideUp(() => {
                        $("#sidePanel").hide();
                    });
                    $("#panelToggleIcon").removeClass("fa-chevron-up").addClass("fa-chevron-down");
                }
            },
            
            // Update move list in panel
            updateMoveList: function() {
                const $moveList = $("#moveList");
                $moveList.empty();
                
                const moves = this.game.history({verbose: true});
                for (let i = 0; i < moves.length; i += 2) {
                    const moveNum = (i / 2) + 1;
                    const whiteMove = moves[i];
                    const blackMove = i + 1 < moves.length ? moves[i + 1] : null;
                    
                    let moveText = moveNum + ". " + whiteMove.san;
                    if (blackMove) {
                        moveText += " " + blackMove.san;
                    }
                    
                    const $moveItem = $("<div>").addClass("move-item")
                        .html(moveText)
                        .data("moveIndex", i)
                        .click(() => {
                            const idx = $moveItem.data("moveIndex");
                            this.currentMoveIndex = idx + (blackMove ? 2 : 1);
                            this.game.load(this.moveHistory[this.currentMoveIndex]);
                            this.board.position(this.moveHistory[this.currentMoveIndex]);
                            this.updateMoveList();
                        });
                    
                    $moveList.append($moveItem);
                }
                
                // Highlight current move
                $(".move-item").removeClass("active");
                if (this.currentMoveIndex > 0) {
                    const currentMove = Math.floor((this.currentMoveIndex - 1) / 2) * 2;
                    $(".move-item[data-move-index='" + currentMove + "']").addClass("active");
                }
            },
            
            // Log info to panel
                const $infoLog = $("#infoLog");
                const $entry = $("<div>").addClass("log-entry").text(message);
                $infoLog.prepend($entry);
                
                // Keep only the last 50 entries
                const entries = $infoLog.children();
                if (entries.length > 50) {
                    entries.slice(50).remove();
                }
            },
            
            // Show AI side selection modal
            showAiSideModal: function() {
                if (this.game.game_over()) {
                    this.displayHint("Game is already over!");
                    return;
                }
                
                const check = this.isValidPosition();
                if (!check.valid) {
                    this.displayHint(check.message);
                    return;
                }
                
                const turn = this.game.turn() === 'w' ? 'White' : 'Black';
                $(".modal-title").html(`AI will play as:<br><small>Current turn: ${turn}</small>`);
                
                $("#aiWhiteBtn").prop("disabled", this.game.turn() !== 'w');
                $("#aiBlackBtn").prop("disabled", this.game.turn() !== 'b');
                $("#aiSideModal").show();
            },
            
                $("#aiSideModal").hide();
                
                if ((side === "white" && this.game.turn() === "b") || 
                    (side === "black" && this.game.turn() === "w")) {
                $("#engineSolveBtn").prop("disabled", true).html('<i class="fas fa-spinner fa-spin"></i> <span>Calculating...</span>');
                $("#playPauseBtn").prop("disabled", true).html('<i class="fas fa-play"></i> <span>Play</span>');
                $("#goBackBtn").prop("disabled", true);
                $("#goForwardBtn").prop("disabled", true);
                
                if (this.userColor === "black") {
                    this.stockfishMove();
                }
                
                $("#hintContainer").hide();
                this.$board.find(".square-55d63").removeClass("hint-move");
                this.updateMoveList();
            },
            
            // Flip board orientation
            flipBoard: function() {
                this.board.flip();
                this.userColor = this.userColor === "white" ? "black" : "white";
            },
            
            // Drag start handler
            onDragStart: function(source, piece) {
                if (this.isEditing) return true;
                if (this.game.game_over()) return false;
                if ((this.game.turn() === "w" && piece.search(/^b/) !== -1) ||
                    (this.game.turn() === "b" && piece.search(/^w/) !== -1)) {
                    return false;
                }
                return true;
            },
            
            // Drop handler
            onDrop: function(source, target) {
                if (this.isEditing) return true;
                
                this.removeGreySquares();

                // Check if this is a promotion move
                const piece = this.game.get(source);
                if (piece && piece.type === 'p' && 
                    ((piece.color === 'w' && target[1] === '8') || 
                     (piece.color === 'b' && target[1] === '1'))) {
                    this.promotionMove = {
                        from: source,
                        to: target,
                        color: piece.color
                    };
                    return 'snapback';
                }

                const move = this.game.move({
                    from: source,
                    to: target,
                    promotion: "q" // Default to queen if promotion is needed
                });

                if (move === null) return "snapback";

                this.handleValidMove(move);
                return true;
            },
            
            // Handle valid move
            handleValidMove: function(move) {
                // Handle variant-specific rules
                if (this.gameVariant === "atomic") {
                    this.handleAtomicMove(move);
                } else if (this.gameVariant === "kingofthehill") {
                    this.handleKingOfTheHillMove(move);
                } else if (this.gameVariant === "threecheck") {
                    this.handleThreeCheckMove(move);
                }
                
                this.addHighlights(move);
                this.board.position(this.game.fen());
                this.updateMoveHistory();
                this.updateMoveList();
                
                if ($("#playPauseBtn").prop("disabled")) {
                    $("#playPauseBtn").prop("disabled", false);
                }
                
                // Handle clock
                if (this.currentClockType !== "none") {
                    this.stopClock();
                $("#goBackBtn").prop("disabled", this.currentMoveIndex <= 0);
                $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
            },
            
            // Promotion dialog handler
                const $dialog = $('<div>').addClass('promotion-dialog');
                
                const pieces = ['q', 'r', 'b', 'n'];
                pieces.forEach((piece) => {
                    const $piece = $('<div>').addClass('promotion-piece')
                        .css('background-image', 'url("' + this.pieceTheme(color + piece.toUpperCase()) + '")')
                        .data('piece', piece)
                        .click(() => {
                            const move = this.game.move({
                                from: source,
                                to: target,
                                promotion: $piece.data('piece')
                            });
                            if (move) {
                                this.handleValidMove(move);
                            }
                            $dialog.remove();
                            callback();
                        });
                    $dialog.append($piece);
                });
                
                $('body').append($dialog);
                
                // Position the dialog near the promotion square
                const $targetSquare = $('.square-' + target);
                const offset = $targetSquare.offset();
                $dialog.css({
                    'left': offset.left + 'px',
                    'top': (offset.top - 180) + 'px'
                });
                
                return false; // Prevent default dialog
            },
            
            // Mouse over square handler
            onMouseoverSquare: function(square, piece) {
                if (!this.game || this.isEditing) return;
                
                const moves = this.game.moves({
                    square: square,
                    verbose: true
                });

                if (moves.length === 0) return;

                this.greySquare(square);

                for (let i = 0; i < moves.length; i++) {
                    this.greySquare(moves[i].to);
                }
            },
            
            // Mouse out square handler
            onMouseoutSquare: function(square, piece) {
                this.removeGreySquares();
            },
            
            // Snap end handler
            onSnapEnd: function() {
                this.board.position(this.game.fen());
            },
            
            // Remove grey squares
            removeGreySquares: function() {
                $("#myBoard .square-55d63").css("background", "");
            },
            
            // Grey square
            greySquare: function(square) {
                const $square = $("#myBoard .square-" + square);
                const background = $square.hasClass("black-3c85d") ? "#696969" : "#a9a9a9";
                $square.css("background", background);
            },
            
            // Add highlights
            addHighlights: function(move) {
                // Clear previous highlights
                this.$board.find(".square-55d63").removeClass("highlight-white highlight-black");
                
                if (this.game.turn() === "b") {
                    this.$board.find(".square-" + move.from).addClass("highlight-white");
                    this.$board.find(".square-" + move.to).addClass("highlight-white");
                } else {
                    this.$board.find(".square-" + move.from).addClass("highlight-black");
                    this.$board.find(".square-" + move.to).addClass("highlight-black");
                }
            },
            
            // Step back in move history
            stepBack: function() {
                if (this.currentMoveIndex <= 0) return;
                
                this.currentMoveIndex--;
                this.game.load(this.moveHistory[this.currentMoveIndex]);
                this.board.position(this.moveHistory[this.currentMoveIndex]);
                this.updateMoveList();
                
                // Update button states
                $("#goBackBtn").prop("disabled", this.currentMoveIndex <= 0);
                $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
                
                if (this.game.history().length === 0) {
                    $("#playPauseBtn").prop("disabled", true);
                    $("#playPauseBtn").html('<i class="fas fa-play"></i> <span>Play</span>');
                }
            },
            
            // Step forward in move history
            stepForward: function() {
                if (this.currentMoveIndex >= this.moveHistory.length - 1) return;
                
                this.currentMoveIndex++;
                this.game.load(this.moveHistory[this.currentMoveIndex]);
                this.board.position(this.moveHistory[this.currentMoveIndex]);
                this.updateMoveList();
                
                // Update button states
                $("#goBackBtn").prop("disabled", this.currentMoveIndex <= 0);
                $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
                
                if (this.game.history().length > 0) {
                    $("#playPauseBtn").prop("disabled", false);
                }
            },
            
            // Make stockfish move
            stockfishMove: function() {
                if (this.game.game_over()) return;
                if ((this.game.turn() === "w" && this.userColor === "white") || 
                    (this.game.turn() === "b" && this.userColor === "black")) {
                    return;
                }

                const pgnText = $("#pgnInput").val().trim();
                const files = $("#pgnFileInput")[0].files;
                
                if (!pgnText && files.length === 0) {
                    this.displayHint("Please enter PGN text or select a file");
                    return;
                }

                // Show loading indicator
                const $loadBtn = $("#loadPgnBtn");
                const originalText = $loadBtn.html();
                $loadBtn.html('<i class="fas fa-spinner fa-spin"></i> Loading...').prop("disabled", true);

                const importFailed = (error) => {
                    console.error("Import failed:", error);
                    this.displayHint("Import failed: " + (error.message || error));
                    $loadBtn.html(originalText).prop("disabled", false);
                };

                try {
                    if (files.length > 0) {
                        // Handle file import
                        const file = files[0];
                        const reader = new FileReader();
                        
                        reader.onload = (e) => {
                            try {
                                const content = e.target.result;
                                if (!content.trim()) {
                                    throw new Error("File is empty");
                                }
                                
                                // Try direct import first
                                try {
                                    this.processPGNImport(content);
                                    this.displayHint("Game loaded successfully from file");
                                    this.hidePgnInput();
                                    $loadBtn.html(originalText).prop("disabled", false);
                                    return;
                                } catch (parseError) {
                                    console.log("Direct import failed, trying multi-game:", parseError);
                                }
                                
                                // Fall back to multi-game import
                                this.handleMultiGameImport(content);
                                $loadBtn.html(originalText).prop("disabled", false);
                            } catch (e) {
                                importFailed(e);
                            }
                        };
                        
                        reader.onerror = () => {
                            importFailed("Error reading file");
                        };
                        
                        reader.readAsText(file);
                    } else {
                        // Handle text import
                        try {
                            this.processPGNImport(pgnText);
                            this.displayHint("Game loaded successfully");
                            this.hidePgnInput();
                            $loadBtn.html(originalText).prop("disabled", false);
                        } catch (parseError) {
                            console.log("Direct import failed, trying multi-game:", parseError);
                            this.handleMultiGameImport(pgnText);
                            $loadBtn.html(originalText).prop("disabled", false);
                        }
                    }
                } catch (e) {
                    importFailed(e);
                }
            },
            
            processPGNImport: function(pgnText) {
                // Create a new game instance
                    $("#databaseSelector").show();
                    this.hidePgnInput();
                    this.displayHint(`Found ${validGames} valid game(s). Select one to load.`);
                } else {
                    throw new Error("No valid games found in the PGN");
                }
            },
            
            // Helper methods
            resetGameState: function() {
                this.moveHistory = [];
                this.currentMoveIndex = 0;
                $("#playPauseBtn").prop("disabled", this.game.history().length === 0)
                    .html('<i class="fas fa-play"></i> <span>Play</span>');
                $("#goBackBtn").prop("disabled", this.currentMoveIndex <= 0);
                $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
                
                // Clear any highlights or hints
                this.$board.find(".square-55d63").removeClass("hint-move highlight-white highlight-black");
                if ($("#pgnOptions").is(":visible")) {
                    this.hidePgnOptions();
                } else {
                    this.showPgnOptions();
                }
            },
            
            // Show PGN options
            showPgnOptions: function() {
                $("#pgnOptions").show();
                $("#pgnContainer").hide();
                $("#databaseSelector").hide();
            },
            
            // Hide PGN options
            hidePgnOptions: function() {
                $("#pgnOptions").hide();
                $("#pgnContainer").hide();
                $("#databaseSelector").hide();
            },
            
            // Show import options
            showImportOptions: function(multiFile) {
                this.hidePgnOptions();
                
                if (multiFile) {
                    $("#pgnFileInput").prop("multiple", true);
                    $("#pgnContainer .file-input-label i").removeClass("fa-file-import").addClass("fa-files");
                    $("#pgnContainer .file-input-label").html('<i class="fas fa-files"></i> Select PGN files');
                } else {
                    $("#pgnFileInput").prop("multiple", false);
                    $("#pgnContainer .file-input-label i").removeClass("fa-files").addClass("fa-file-import");
                    $("#pgnContainer .file-input-label").html('<i class="fas fa-file-import"></i> Select PGN file');
                }
                
                $("#pgnContainer").show();
                $("#pgnInput").val("").focus();
            },
            
            // Hide PGN input
            hidePgnInput: function() {
                $("#pgnContainer").hide();
                $("#pgnInput").val("");
                $("#pgnFileInput").val("");
                this.hidePgnOptions();
            },
            
            // Hide database selector
            hideDatabaseSelector: function() {
                $("#databaseSelector").hide();
                this.hidePgnOptions();
            },
            
            // Toggle play/pause
            togglePlayPause: function() {
                if (this.isPlaying) {
                    this.pausePlayback();
                } else {
                    this.startPlayback();
                }
            },
            
            // Start playback
            startPlayback: function() {
                if (this.game.history().length === 0) {
                    this.displayHint("No moves to play back");
                    return;
                }
                
                this.isPlaying = true;
                $("#playPauseBtn").html('<i class="fas fa-pause"></i> <span>Pause</span>');
                
                if (this.currentMoveIndex >= this.moveHistory.length - 1) {
                    this.currentMoveIndex = 0;
                    this.game.load(this.moveHistory[0]);
                    this.board.position(this.moveHistory[0]);
                    this.updateMoveList();
                }
                
                this.playInterval = setInterval(() => {
                    if (this.currentMoveIndex >= this.moveHistory.length - 1) {
                        this.pausePlayback();
                        return;
                    }
                    
                    this.currentMoveIndex++;
                    this.game.load(this.moveHistory[this.currentMoveIndex]);
                    this.board.position(this.moveHistory[this.currentMoveIndex]);
                    this.updateMoveList();
                    
                    // Update button states
                    $("#goBackBtn").prop("disabled", this.currentMoveIndex <= 0);
                    $("#goForwardBtn").prop("disabled", this.currentMoveIndex >= this.moveHistory.length - 1);
                    
                }, 1000);
            },
            
            // Pause playback
            pausePlayback: function() {
                this.isPlaying = false;
                clearInterval(this.playInterval);
                $("#playPauseBtn").html('<i class="fas fa-play"></i> <span>Play</span>');
            },
            
            // Login functions
            showLoginModal: function() {
                $("#loginModal").show();
                $("#loginMessage").hide();
            },
            
            hideLoginModal: function() {
                $("#loginModal").hide();
                $("#loginEmail").val("");
                $("#loginPassword").val("");
                $("#loginMessage").hide();
            },
            
            checkLoginStatus: function() {
                const user = localStorage.getItem("chessUser");
                if (user) {
                    const userObj = JSON.parse(user);
                    $("#signinBtn").html('<i class="fas fa-user"></i> <span>' + userObj.email + '</span>');
                    $("#signinBtn").removeClass("not-signed-in").addClass("signed-in");
                    $("#engineSelect option[value='server']").prop("disabled", false);
                }
            },
            
            handleLogin: function() {
                const email = $("#loginEmail").val().trim();
                const password = $("#loginPassword").val().trim();
                
                if (!email || !password) {
                    this.showLoginMessage("Please enter both email and password", false);
                    return;
                }
                
                // In a real app, you would send this to your server
                this.mockLogin(email, password, (success, message) => {
                    if (success) {
                        this.showLoginMessage(message, true);
                        localStorage.setItem("chessUser", JSON.stringify({ email: email }));
                        $("#signinBtn").html('<i class="fas fa-user"></i> <span>' + email + '</span>');
                        $("#signinBtn").removeClass("not-signed-in").addClass("signed-in");
                        $("#engineSelect option[value='server']").prop("disabled", false);
                        setTimeout(this.hideLoginModal.bind(this), 1500);
                    } else {
                        this.showLoginMessage(message, false);
                    }
                });
            },
            
            handleRegister: function() {
                const email = $("#loginEmail").val().trim();
                const password = $("#loginPassword").val().trim();
                
                if (!email || !password) {
                    this.showLoginMessage("Please enter both email and password", false);
                    return;
                }
                
                // In a real app, you would send this to your server
                this.mockRegister(email, password, (success, message) => {
                    if (success) {
                        this.showLoginMessage(message, true);
                        localStorage.setItem("chessUser", JSON.stringify({ email: email }));
                        $("#signinBtn").html('<i class="fas fa-user"></i> <span>' + email + '</span>');
                        $("#signinBtn").removeClass("not-signed-in").addClass("signed-in");
                        $("#engineSelect option[value='server']").prop("disabled", false);
                        setTimeout(this.hideLoginModal.bind(this), 1500);
                    } else {
                        this.showLoginMessage(message, false);
                    }
                });
            },
            
            showLoginMessage: function(message, isSuccess) {
                const $msg = $("#loginMessage");
                $msg.text(message).show();
                $msg.toggleClass("login-success", isSuccess);
            },
            
            // Mock server functions (replace with real API calls)
            mockLogin: function(email, password, callback) {
                setTimeout(() => {
                    // Check if user exists in localStorage
                    const storedUser = localStorage.getItem("chessUser");
                    if (storedUser) {
                        const userObj = JSON.parse(storedUser);
                        if (userObj.email === email) {
                            callback(true, "Login successful!");
                        } else {
                            callback(false, "Invalid email or password");
                        }
                    } else {
                        callback(false, "User not found. Please register.");
                    }
                }, 500);
            },
            
            mockRegister: function(email, password, callback) {
                setTimeout(() => {
                    // Check if user already exists
                    const storedUser = localStorage.getItem("chessUser");
                    if (storedUser && JSON.parse(storedUser).email === email) {
                        callback(false, "Email already registered");
                    } else {
                        // In a real app, you would store this on your server
                        localStorage.setItem("chessUser", JSON.stringify({ email: email }));
                        callback(true, "Registration successful!");
                    }
                }, 500);
            }
        };

        $(document).ready(() => {
            ChessGame.init();
        });
    

// === Utility Functions ===
                function formatTime(seconds) {
                    const mins = Math.floor(seconds / 60);
                    const secs = seconds % 60;
                    return mins + ":" + (secs < 10 ? "0" : "") + secs;
                }
                
            logInfo: function(message) {
            onPromotionDialog: function(source, target, callback) {
                const color = this.game.get(source).color;

// === Miscellaneous ===

<!-- Enhanced JavaScript with all improvements -->

// Sound effects
const soundEffects = {
    move: new Audio('https://www.soundjay.com/mechanical/sounds/chess-move-01.mp3'),
    capture: new Audio('https://www.soundjay.com/mechanical/sounds/chess-capture-01.mp3'),
    check: new Audio('https://www.soundjay.com/mechanical/sounds/chess-check-01.mp3'),
    gameEnd: new Audio('https://www.soundjay.com/mechanical/sounds/chess-game-end-01.mp3')
};

// Sound toggle
let soundEnabled = true;
$('#soundToggleBtn').click(function() {
    soundEnabled = !soundEnabled;
    $(this).find('i').toggleClass('fa-volume-up fa-volume-mute');
    localStorage.setItem('chessSoundEnabled', soundEnabled);
});

// Load sound preference
if (localStorage.getItem('chessSoundEnabled') === 'false') {
    soundEnabled = false;
    $('#soundToggleBtn i').removeClass('fa-volume-up').addClass('fa-volume-mute');
}

// Error handling
function showError(message) {
    const errorElement = $('#errorMessage');
    errorElement.text(message).fadeIn();
    setTimeout(() => errorElement.fadeOut(), 5000);
    
    if (soundEnabled) {
        soundEffects.gameEnd.play().catch(e => console.log('Sound playback error:', e));
    }
}

// Loading states
function showLoading(message = 'Loading...') {
    $('#loadingText').text(message);
    $('#loadingOverlay').fadeIn();
}

function hideLoading() {
    $('#loadingOverlay').fadeOut();
}

// Tutorial system
$('#helpBtn').click(function() {
    $('#tutorialModal').fadeIn();
});

$('#closeTutorialBtn').click(function() {
    $('#tutorialModal').fadeOut();
});

// Engine initialization with error handling
function initEngine() {
    showLoading('Initializing chess engine...');
    
    try {
        // Your existing engine initialization code
        // Add error handling around it
        
        // Simulate engine loading
        setTimeout(() => {
            hideLoading();
            // Set up engine event listeners
            setupEngineListeners();
        }, 1500);
    } catch (error) {
        hideLoading();
        showError('Failed to initialize chess engine: ' + error.message);
        console.error('Engine initialization error:', error);
    }
}

// Setup engine listeners
function setupEngineListeners() {
    // Your existing engine event listeners
    // Add error handling for each event
    
    // Example:
    chessEngine.on('error', (error) => {
        showError('Engine error: ' + error.message);
    });
    
    chessEngine.on('move', (move) => {
        if (soundEnabled) {
            soundEffects.move.play().catch(e => console.log('Sound playback error:', e));
        }
        // Update board
    });
}

// Initialize the app
$(document).ready(function() {
    // Check for errors in dependencies
    if (typeof Chess === 'undefined') {
        showError('Chess.js failed to load. Please refresh the page.');
        return;
    }
    
    if (typeof ChessBoard === 'undefined') {
        showError('Chessboard.js failed to load. Please refresh the page.');
        return;
    }
    
    // Initialize with error handling
    try {
        initEngine();
        
        // Load user preferences from localStorage
        loadPreferences();
        
        // Set up all event listeners
        setupEventListeners();
    } catch (error) {
        showError('Application initialization failed: ' + error.message);
        console.error('Initialization error:', error);
    }
});

// Local storage for preferences
function loadPreferences() {
    const savedTheme = localStorage.getItem('chessTheme') || 'default';
    $(`[data-theme="${savedTheme}"]`).click();
    
    const savedPieceTheme = localStorage.getItem('chessPieceTheme') || 'default';
    $(`[data-piece-theme="${savedPieceTheme}"]`).click();
}

// Setup all event listeners
function setupEventListeners() {
    // Your existing event listeners
    // Add error handling to each
    
    // Example:
    $('#startBtn').click(function() {
        try {
            // New game logic
        } catch (error) {
            showError('Failed to start new game: ' + error.message);
        }
    });
    
    // Add loading state to engine operations
    $('#engineSolveBtn').click(function() {
        showLoading('Engine analyzing...');
        // Your engine solve logic
    });
}

// Move validation feedback
function onMove(source, target) {
    try {
        // Your move validation logic
        // Add sound effects
        if (soundEnabled) {
            if (isCaptureMove(source, target)) {
                soundEffects.capture.play().catch(e => console.log('Sound playback error:', e));
            } else {
                soundEffects.move.play().catch(e => console.log('Sound playback error:', e));
            }
        }
    } catch (error) {
        showError('Invalid move: ' + error.message);
        return 'snapback';
    }
}

// Responsive adjustments
function handleResize() {
    if ($(window).width() < 768) {
        // Mobile adjustments
    } else {
        // Desktop adjustments
    }
}

$(window).resize(handleResize);
handleResize(); // Initial call

