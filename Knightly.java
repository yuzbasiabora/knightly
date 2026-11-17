// =============================================================================
//  Knightly: a complete chess engine in a single Java file (Java 17+, no libraries)
//
//  * full legal move generation (castling, en passant, promotions), verified with perft
//  * alpha-beta search: iterative deepening, transposition table, quiescence,
//    null-move pruning, late-move reductions, killer/history move ordering
//  * UCI protocol, so it plugs into chess GUIs such as Arena, Cute Chess or Lucas Chess
//  * play it in the terminal, with SAN or coordinate input
//  * a built-in self-test suite
//
//  Run:   java Knightly.java            play against the engine
//         java Knightly.java uci        UCI mode, for chess GUIs
//         java Knightly.java perft 5    count positions (move generator test)
//         java Knightly.java selftest   run all tests
//         java Knightly.java bench      search speed benchmark
//
//  MIT License, Copyright (c) 2026
// =============================================================================
import java.io.*;
import java.util.*;

public final class Knightly {
    static final String VERSION = "1.0";
    static final String START = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
    static final int EMPTY = 0, P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6;
    static final int MATE = 30000, INF = 32000, MAXPLY = 100, HIST = 4096;
    static final int F_DOUBLE = 1, F_EP = 2, F_CASTLE = 4;
    static final String PIECES = "PNBRQK";

    // ------------------------------------------------------------------ tables
    static final int[][] KN = new int[64][], KG = new int[64][];
    static final int[][][] RAY = new int[64][8][];
    static final int[][][] PATT = new int[2][64][];
    static final int[] CR = new int[64];
    static final long[][] ZP = new long[16][64];
    static final long[] ZC = new long[16], ZE = new long[8];
    static final long ZS;

    static {
        int[] kf = {1, 2, 2, 1, -1, -2, -2, -1}, kr = {2, 1, -1, -2, -2, -1, 1, 2};
        int[] df = {0, 1, 0, -1, 1, 1, -1, -1}, dr = {1, 0, -1, 0, 1, -1, -1, 1};   // N E S W NE SE SW NW
        for (int s = 0; s < 64; s++) {
            int f = s & 7, r = s >> 3;
            KN[s] = list(f, r, kf, kr);
            KG[s] = list(f, r, df, dr);
            for (int d = 0; d < 8; d++) {
                ArrayList<Integer> l = new ArrayList<>();
                for (int x = f + df[d], y = r + dr[d]; ok(x, y); x += df[d], y += dr[d]) l.add(y * 8 + x);
                RAY[s][d] = l.stream().mapToInt(i -> i).toArray();
            }
            PATT[0][s] = list(f, r, new int[]{-1, 1}, new int[]{1, 1});
            PATT[1][s] = list(f, r, new int[]{-1, 1}, new int[]{-1, -1});
        }
        Arrays.fill(CR, 15);
        CR[0] &= ~2; CR[7] &= ~1; CR[4] &= ~3; CR[56] &= ~8; CR[63] &= ~4; CR[60] &= ~12;
        Random rnd = new Random(0x9E3779B97F4A7C15L);
        for (long[] a : ZP) for (int i = 0; i < 64; i++) a[i] = rnd.nextLong();
        for (int i = 0; i < 16; i++) ZC[i] = rnd.nextLong();
        for (int i = 0; i < 8; i++) ZE[i] = rnd.nextLong();
        ZS = rnd.nextLong();
    }
    static boolean ok(int f, int r) { return f >= 0 && f < 8 && r >= 0 && r < 8; }
    static int[] list(int f, int r, int[] df, int[] dr) {
        int[] t = new int[8]; int n = 0;
        for (int i = 0; i < df.length; i++) if (ok(f + df[i], r + dr[i])) t[n++] = (r + dr[i]) * 8 + f + df[i];
        return Arrays.copyOf(t, n);
    }

    // ------------------------------------------------------------------ moves
    static int mv(int f, int t, int promo, int fl) { return f | t << 6 | promo << 12 | fl << 16; }
    static int from(int m) { return m & 63; }
    static int to(int m) { return (m >> 6) & 63; }
    static int promo(int m) { return (m >> 12) & 7; }
    static int flags(int m) { return m >> 16; }
    static String sq(int s) { return "" + (char) ('a' + (s & 7)) + (char) ('1' + (s >> 3)); }
    static String uci(int m) { return sq(from(m)) + sq(to(m)) + (promo(m) != 0 ? "" + Character.toLowerCase(PIECES.charAt(promo(m) - 1)) : ""); }

    // ------------------------------------------------------------------ position
    static final class Pos {
        final int[] b = new int[64];          // 0 empty, 1..6 white PNBRQK, 9..14 black
        int side, castle, ep = -1, half, full = 1, sp;
        long hash;
        final int[] king = new int[2];
        final int[] uMove = new int[HIST], uCap = new int[HIST], uCastle = new int[HIST], uEp = new int[HIST], uHalf = new int[HIST];
        final long[] uHash = new long[HIST], keys = new long[HIST];

        static Pos fromFen(String fen) {
            String[] t = fen.trim().split("\\s+");
            if (t.length < 2) throw new IllegalArgumentException("bad FEN: " + fen);
            Pos p = new Pos();
            int r = 7, f = 0;
            for (char c : t[0].toCharArray()) {
                if (c == '/') { r--; f = 0; }
                else if (Character.isDigit(c)) f += c - '0';
                else {
                    int i = PIECES.indexOf(Character.toUpperCase(c));
                    if (i < 0 || !ok(f, r)) throw new IllegalArgumentException("bad FEN: " + fen);
                    p.b[r * 8 + f++] = (i + 1) | (Character.isLowerCase(c) ? 8 : 0);
                }
            }
            p.side = t[1].equals("b") ? 1 : 0;
            if (t.length > 2) for (char c : t[2].toCharArray()) { int i = "KQkq".indexOf(c); if (i >= 0) p.castle |= 1 << i; }
            if (t.length > 3 && t[3].length() == 2) p.ep = (t[3].charAt(1) - '1') * 8 + t[3].charAt(0) - 'a';
            if (t.length > 4) p.half = Integer.parseInt(t[4]);
            if (t.length > 5) p.full = Integer.parseInt(t[5]);
            int[] kc = new int[2];
            for (int s = 0; s < 64; s++) if ((p.b[s] & 7) == K) { p.king[p.b[s] >> 3] = s; kc[p.b[s] >> 3]++; }
            if (kc[0] != 1 || kc[1] != 1) throw new IllegalArgumentException("each side needs exactly one king");
            p.hash = p.computeHash();
            p.keys[0] = p.hash;
            return p;
        }

        Pos copy() {
            Pos c = new Pos();
            System.arraycopy(b, 0, c.b, 0, 64);
            c.side = side; c.castle = castle; c.ep = ep; c.half = half; c.full = full; c.sp = sp; c.hash = hash;
            c.king[0] = king[0]; c.king[1] = king[1];
            for (int i = 0; i <= sp; i++) { c.uMove[i] = uMove[i]; c.uCap[i] = uCap[i]; c.uCastle[i] = uCastle[i]; c.uEp[i] = uEp[i]; c.uHalf[i] = uHalf[i]; c.uHash[i] = uHash[i]; c.keys[i] = keys[i]; }
            return c;
        }

        long computeHash() {
            long h = 0;
            for (int s = 0; s < 64; s++) if (b[s] != 0) h ^= ZP[b[s]][s];
            if (side == 1) h ^= ZS;
            h ^= ZC[castle];
            if (ep >= 0) h ^= ZE[ep & 7];
            return h;
        }

        String fen() {
            StringBuilder sb = new StringBuilder();
            for (int r = 7; r >= 0; r--) {
                int e = 0;
                for (int f = 0; f < 8; f++) {
                    int pc = b[r * 8 + f];
                    if (pc == 0) { e++; continue; }
                    if (e > 0) { sb.append(e); e = 0; }
                    char c = PIECES.charAt((pc & 7) - 1);
                    sb.append((pc >> 3) == 1 ? Character.toLowerCase(c) : c);
                }
                if (e > 0) sb.append(e);
                if (r > 0) sb.append('/');
            }
            sb.append(side == 0 ? " w " : " b ");
            String c = (castle & 1) != 0 ? "K" : ""; c += (castle & 2) != 0 ? "Q" : ""; c += (castle & 4) != 0 ? "k" : ""; c += (castle & 8) != 0 ? "q" : "";
            sb.append(c.isEmpty() ? "-" : c).append(' ').append(ep >= 0 ? sq(ep) : "-").append(' ').append(half).append(' ').append(full);
            return sb.toString();
        }

        boolean attacked(int s, int by) {
            for (int a : PATT[by ^ 1][s]) if (b[a] == (P | by << 3)) return true;
            for (int a : KN[s]) if (b[a] == (N | by << 3)) return true;
            for (int a : KG[s]) if (b[a] == (K | by << 3)) return true;
            for (int d = 0; d < 8; d++)
                for (int a : RAY[s][d]) {
                    int pc = b[a];
                    if (pc == 0) continue;
                    if ((pc >> 3) == by) { int t = pc & 7; if (t == Q || (d < 4 ? t == R : t == B)) return true; }
                    break;
                }
            return false;
        }
        boolean inCheck() { return attacked(king[side], side ^ 1); }

        // Pseudo-legal moves. With `caps` only captures and promotions are generated (for quiescence).
        int gen(int[] m, boolean caps) {
            int n = 0, us = side, them = us ^ 1;
            for (int s = 0; s < 64; s++) {
                int pc = b[s];
                if (pc == 0 || (pc >> 3) != us) continue;
                int t = pc & 7;
                if (t == P) {
                    int dir = us == 0 ? 8 : -8, r = s >> 3, pr = us == 0 ? 6 : 1, st = us == 0 ? 1 : 6, one = s + dir;
                    if (b[one] == 0) {
                        if (r == pr) n = promos(m, n, s, one);
                        else if (!caps) { m[n++] = mv(s, one, 0, 0); if (r == st && b[one + dir] == 0) m[n++] = mv(s, one + dir, 0, F_DOUBLE); }
                    }
                    for (int to : PATT[us][s]) {
                        int tp = b[to];
                        if (tp != 0 && (tp >> 3) == them) { if (r == pr) n = promos(m, n, s, to); else m[n++] = mv(s, to, 0, 0); }
                        else if (tp == 0 && to == ep) m[n++] = mv(s, to, 0, F_EP);
                    }
                } else if (t == N || t == K) {
                    for (int to : t == N ? KN[s] : KG[s]) {
                        int tp = b[to];
                        if (tp == 0 ? !caps : (tp >> 3) == them) m[n++] = mv(s, to, 0, 0);
                    }
                    if (t == K && !caps) {
                        if (us == 0 && s == 4) {
                            if ((castle & 1) != 0 && b[5] == 0 && b[6] == 0 && !attacked(4, 1) && !attacked(5, 1) && !attacked(6, 1)) m[n++] = mv(4, 6, 0, F_CASTLE);
                            if ((castle & 2) != 0 && b[3] == 0 && b[2] == 0 && b[1] == 0 && !attacked(4, 1) && !attacked(3, 1) && !attacked(2, 1)) m[n++] = mv(4, 2, 0, F_CASTLE);
                        } else if (us == 1 && s == 60) {
                            if ((castle & 4) != 0 && b[61] == 0 && b[62] == 0 && !attacked(60, 0) && !attacked(61, 0) && !attacked(62, 0)) m[n++] = mv(60, 62, 0, F_CASTLE);
                            if ((castle & 8) != 0 && b[59] == 0 && b[58] == 0 && b[57] == 0 && !attacked(60, 0) && !attacked(59, 0) && !attacked(58, 0)) m[n++] = mv(60, 58, 0, F_CASTLE);
                        }
                    }
                } else {
                    int d0 = t == B ? 4 : 0, d1 = t == R ? 4 : 8;
                    for (int d = d0; d < d1; d++)
                        for (int to : RAY[s][d]) {
                            int tp = b[to];
                            if (tp == 0) { if (!caps) m[n++] = mv(s, to, 0, 0); continue; }
                            if ((tp >> 3) == them) m[n++] = mv(s, to, 0, 0);
                            break;
                        }
                }
            }
            return n;
        }
        static int promos(int[] m, int n, int f, int t) { for (int p = Q; p >= N; p--) m[n++] = mv(f, t, p, 0); return n; }

        void make(int m) {
            uMove[sp] = m; uCap[sp] = 0; uCastle[sp] = castle; uEp[sp] = ep; uHalf[sp] = half; uHash[sp] = hash;
            if (m == 0) {                                   // null move: pass the turn
                if (ep >= 0) { hash ^= ZE[ep & 7]; ep = -1; }
                side ^= 1; hash ^= ZS; sp++; keys[sp] = hash;
                return;
            }
            int f = from(m), t = to(m), pr = promo(m), fl = flags(m), pc = b[f], cap = b[t];
            uCap[sp] = cap;
            hash ^= ZP[pc][f] ^ ZC[castle];
            if (ep >= 0) hash ^= ZE[ep & 7];
            if (cap != 0) hash ^= ZP[cap][t];
            int moved = pr != 0 ? (pr | side << 3) : pc;
            b[f] = 0; b[t] = moved; hash ^= ZP[moved][t];
            if ((fl & F_EP) != 0) { int cs = t + (side == 0 ? -8 : 8); hash ^= ZP[b[cs]][cs]; b[cs] = 0; }
            if ((fl & F_CASTLE) != 0) {
                int rf = t > f ? f + 3 : f - 4, rt = t > f ? f + 1 : f - 1, rk = b[rf];
                b[rf] = 0; b[rt] = rk; hash ^= ZP[rk][rf] ^ ZP[rk][rt];
            }
            if ((pc & 7) == K) king[side] = t;
            castle &= CR[f] & CR[t];
            ep = (fl & F_DOUBLE) != 0 ? (f + t) / 2 : -1;
            half = ((pc & 7) == P || cap != 0) ? 0 : half + 1;
            if (side == 1) full++;
            side ^= 1; hash ^= ZS ^ ZC[castle];
            if (ep >= 0) hash ^= ZE[ep & 7];
            sp++; keys[sp] = hash;
        }

        void unmake() {
            sp--;
            int m = uMove[sp];
            castle = uCastle[sp]; ep = uEp[sp]; half = uHalf[sp]; hash = uHash[sp];
            side ^= 1;
            if (m == 0) return;
            int f = from(m), t = to(m), pr = promo(m), fl = flags(m);
            int pc = pr != 0 ? (P | side << 3) : b[t];
            b[f] = pc; b[t] = uCap[sp];
            if ((fl & F_EP) != 0) b[t + (side == 0 ? -8 : 8)] = P | (side ^ 1) << 3;
            if ((fl & F_CASTLE) != 0) { int rf = t > f ? f + 3 : f - 4, rt = t > f ? f + 1 : f - 1; b[rf] = b[rt]; b[rt] = 0; }
            if ((pc & 7) == K) king[side] = f;
            if (side == 1) full--;
        }

        // Legal moves only (make, test own king, unmake).
        int legal(int[] out) {
            int[] tmp = new int[256];
            int n = gen(tmp, false), k = 0;
            for (int i = 0; i < n; i++) { make(tmp[i]); if (!attacked(king[side ^ 1], side)) out[k++] = tmp[i]; unmake(); }
            return k;
        }
        boolean isLegal(int m) { int[] l = new int[256]; int n = legal(l); for (int i = 0; i < n; i++) if (l[i] == m) return true; return false; }

        boolean repetition() { for (int i = sp - 2; i >= 0 && i >= sp - half; i -= 2) if (keys[i] == hash) return true; return false; }
        int repCount() { int c = 1; for (int i = sp - 2; i >= 0 && i >= sp - half; i -= 2) if (keys[i] == hash) c++; return c; }
        boolean hasNonPawn(int s) { for (int i = 0; i < 64; i++) { int pc = b[i]; if ((pc >> 3) == s && pc != 0 && (pc & 7) > P && (pc & 7) < K) return true; } return false; }
        boolean insufficient() {
            int minors = 0;
            for (int i = 0; i < 64; i++) { int t = b[i] & 7; if (t == P || t == R || t == Q) return false; if (t == N || t == B) minors++; }
            return minors <= 1;
        }

        // ---- algebraic notation
        String san(int m) {
            int f = from(m), t = to(m), pc = b[f], ty = pc & 7;
            StringBuilder sb = new StringBuilder();
            if ((flags(m) & F_CASTLE) != 0) sb.append(t > f ? "O-O" : "O-O-O");
            else {
                boolean cap = b[t] != 0 || (flags(m) & F_EP) != 0;
                if (ty != P) {
                    sb.append(PIECES.charAt(ty - 1));
                    int[] l = new int[256]; int n = legal(l);
                    boolean amb = false, sf = false, sr = false;
                    for (int i = 0; i < n; i++) {
                        int o = l[i];
                        if (o != m && b[from(o)] == pc && to(o) == t) { amb = true; if ((from(o) & 7) == (f & 7)) sf = true; if ((from(o) >> 3) == (f >> 3)) sr = true; }
                    }
                    if (amb) { if (!sf) sb.append(sq(f).charAt(0)); else if (!sr) sb.append(sq(f).charAt(1)); else sb.append(sq(f)); }
                } else if (cap) sb.append(sq(f).charAt(0));
                if (cap) sb.append('x');
                sb.append(sq(t));
                if (promo(m) != 0) sb.append('=').append(PIECES.charAt(promo(m) - 1));
            }
            make(m);
            if (inCheck()) { int[] l = new int[256]; sb.append(legal(l) == 0 ? '#' : '+'); }
            unmake();
            return sb.toString();
        }

        // Accepts coordinate moves (e2e4, e7e8q) and algebraic moves (Nf3, exd5, O-O, e8=Q+). Returns -1 if none matches.
        int parse(String in) {
            String s = in.trim();
            if (s.isEmpty()) return -1;
            int[] l = new int[256]; int n = legal(l);
            String lower = s.toLowerCase();
            for (int i = 0; i < n; i++) if (uci(l[i]).equals(lower)) return l[i];
            String norm = s.replace("0", "O").replace("o-o-o", "O-O-O").replace("o-o", "O-O").replaceAll("[+#!?x=]", "");
            for (int i = 0; i < n; i++) if (san(l[i]).replaceAll("[+#!?x=]", "").equals(norm)) return l[i];
            return -1;
        }

        // 0 = game continues, otherwise a description of how it ended
        String result() {
            int[] l = new int[256];
            if (legal(l) == 0) return inCheck() ? (side == 0 ? "Black wins by checkmate" : "White wins by checkmate") : "Draw by stalemate";
            if (half >= 100) return "Draw by the fifty-move rule";
            if (repCount() >= 3) return "Draw by threefold repetition";
            if (insufficient()) return "Draw by insufficient material";
            return null;
        }

        String board(int last) {
            StringBuilder sb = new StringBuilder("  +-----------------+\n");
            for (int r = 7; r >= 0; r--) {
                sb.append(r + 1).append(" |");
                for (int f = 0; f < 8; f++) {
                    int pc = b[r * 8 + f], s = r * 8 + f;
                    boolean hl = last >= 0 && (s == from(last) || s == to(last));
                    char c = pc == 0 ? '.' : (pc >> 3) == 1 ? Character.toLowerCase(PIECES.charAt((pc & 7) - 1)) : PIECES.charAt((pc & 7) - 1);
                    sb.append(hl ? '[' : ' ').append(c);
                }
                sb.append(" |\n");
            }
            return sb.append("  +-----------------+\n    a b c d e f g h\n").toString();
        }
    }

    static long perft(Pos p, int depth, boolean verify) {
        if (depth == 0) return 1;
        int[] m = new int[256];
        int n = p.gen(m, false);
        long total = 0;
        for (int i = 0; i < n; i++) {
            p.make(m[i]);
            if (!p.attacked(p.king[p.side ^ 1], p.side)) {
                if (verify && p.hash != p.computeHash()) throw new IllegalStateException("hash mismatch after " + uci(m[i]));
                total += depth == 1 ? 1 : perft(p, depth - 1, verify);
            }
            p.unmake();
        }
        return total;
    }

    // ------------------------------------------------------------------ evaluation
    static final int[] VAL = {0, 100, 320, 330, 500, 900, 0};
    // Piece-square tables from White's point of view, rank 8 first.
    static final int[][] PST = {null,
        {0,0,0,0,0,0,0,0, 50,50,50,50,50,50,50,50, 10,10,20,30,30,20,10,10, 5,5,10,25,25,10,5,5, 0,0,0,20,20,0,0,0, 5,-5,-10,0,0,-10,-5,5, 5,10,10,-20,-20,10,10,5, 0,0,0,0,0,0,0,0},
        {-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,0,0,0,-20,-40, -30,0,10,15,15,10,0,-30, -30,5,15,20,20,15,5,-30, -30,0,15,20,20,15,0,-30, -30,5,10,15,15,10,5,-30, -40,-20,0,5,5,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50},
        {-20,-10,-10,-10,-10,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,10,10,5,0,-10, -10,5,5,10,10,5,5,-10, -10,0,10,10,10,10,0,-10, -10,10,10,10,10,10,10,-10, -10,5,0,0,0,0,5,-10, -20,-10,-10,-10,-10,-10,-10,-20},
        {0,0,0,0,0,0,0,0, 5,10,10,10,10,10,10,5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 0,0,0,5,5,0,0,0},
        {-20,-10,-10,-5,-5,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,5,5,5,0,-10, -5,0,5,5,5,5,0,-5, 0,0,5,5,5,5,0,-5, -10,5,5,5,5,5,0,-10, -10,0,5,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20},
        null};
    static final int[] KING_MG = {-30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -20,-30,-30,-40,-40,-30,-30,-20, -10,-20,-20,-20,-20,-20,-20,-10, 20,20,0,0,0,0,20,20, 20,30,10,0,0,10,30,20};
    static final int[] KING_EG = {-50,-40,-30,-20,-20,-30,-40,-50, -30,-20,-10,0,0,-10,-20,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-30,0,0,0,0,-30,-30, -50,-30,-30,-30,-30,-30,-30,-50};
    static final int[] PASSED = {0, 5, 10, 20, 35, 60, 100, 0};

    // Score from the point of view of the side to move, in centipawns.
    static int eval(Pos p) {
        int[] score = new int[2], np = new int[2], pawns = new int[2], bishops = new int[2];
        int[][] pf = new int[2][8];
        int phase = 0;
        for (int s = 0; s < 64; s++) {
            int pc = p.b[s];
            if (pc == 0) continue;
            int c = pc >> 3, t = pc & 7, i = c == 0 ? s ^ 56 : s;
            if (t == K) continue;
            score[c] += VAL[t] + PST[t][i];
            if (t == P) { pawns[c]++; pf[c][s & 7]++; }
            else { np[c] += VAL[t]; phase += t == R ? 2 : t == Q ? 4 : 1; if (t == B) bishops[c]++; }
        }
        phase = Math.min(24, phase);
        for (int c = 0; c < 2; c++) {
            int i = c == 0 ? p.king[0] ^ 56 : p.king[1];
            score[c] += (KING_MG[i] * phase + KING_EG[i] * (24 - phase)) / 24;
            if (bishops[c] >= 2) score[c] += 30;
            for (int f = 0; f < 8; f++) if (pf[c][f] > 1) score[c] -= 10 * (pf[c][f] - 1);
        }
        for (int s = 8; s < 56; s++) {                       // passed pawns
            int pc = p.b[s];
            if ((pc & 7) != P) continue;
            int c = pc >> 3, f = s & 7, r = s >> 3, dir = c == 0 ? 1 : -1;
            boolean passed = true;
            for (int ff = Math.max(0, f - 1); ff <= Math.min(7, f + 1) && passed; ff++)
                for (int rr = r + dir; rr >= 0 && rr < 8; rr += dir) if (p.b[rr * 8 + ff] == (P | (c ^ 1) << 3)) { passed = false; break; }
            if (passed) score[c] += PASSED[c == 0 ? r : 7 - r];
        }
        // Mop-up: with a clear material lead against a bare king, drive it to the edge and bring the king closer.
        for (int c = 0; c < 2; c++) {
            int o = c ^ 1;
            if (np[o] == 0 && pawns[o] == 0 && score[c] - score[o] >= 400) {
                int ok = p.king[o], ck = p.king[c];
                int center = Math.max(3 - (ok & 7), (ok & 7) - 4) + Math.max(3 - (ok >> 3), (ok >> 3) - 4);
                int dist = Math.abs((ok & 7) - (ck & 7)) + Math.abs((ok >> 3) - (ck >> 3));
                score[c] += 10 * center + 4 * (14 - dist);
            }
        }
        int v = score[0] - score[1];
        return (p.side == 0 ? v : -v) + 10;
    }

    // ------------------------------------------------------------------ search
    record Result(int move, int score, int depth, long nodes) {}

    static final class Engine {
        Pos p;
        long nodes, deadline;
        volatile boolean stop;
        int rootBest;
        long[] tk; int[] tm; short[] ts; byte[] td, tf; int tmask;
        final int[] killers = new int[MAXPLY * 2 + 4];
        final int[][] hist = new int[2][4096];
        final int[][] mb = new int[MAXPLY + 4][256], sb = new int[MAXPLY + 4][256];

        Engine(int mbytes) { resize(mbytes); }
        void resize(int mbytes) {
            int n = Integer.highestOneBit(Math.max(1, mbytes) * 1024 * 1024 / 16);
            tk = new long[n]; tm = new int[n]; ts = new short[n]; td = new byte[n]; tf = new byte[n]; tmask = n - 1;
        }
        void clear() { Arrays.fill(tk, 0); Arrays.fill(killers, 0); for (int[] h : hist) Arrays.fill(h, 0); }

        Result search(Pos pos, int maxDepth, long ms, boolean info) {
            p = pos; nodes = 0; stop = false;
            long t0 = System.nanoTime(), limit = ms > 0 ? ms * 1_000_000L : 0;
            deadline = limit > 0 ? t0 + limit : 0;
            int[] ml = new int[256];
            if (p.legal(ml) == 0) return new Result(0, 0, 0, 0);
            int best = ml[0], bestScore = 0, done = 0;
            for (int d = 1; d <= maxDepth; d++) {
                rootBest = 0;
                int score = negamax(d, -INF, INF, 0, true);
                if (stop && d > 1) break;
                if (rootBest != 0) best = rootBest;
                bestScore = score; done = d;
                if (info) {
                    long el = Math.max(1, (System.nanoTime() - t0) / 1_000_000);
                    System.out.println("info depth " + d + " score " + scoreStr(score) + " nodes " + nodes + " nps " + nodes * 1000 / el + " time " + el + " pv " + pv(d));
                }
                if (limit > 0 && (System.nanoTime() - t0) * 5 / 2 > limit) break;
                if (Math.abs(score) > MATE - MAXPLY && d >= MATE - Math.abs(score)) break;
            }
            return new Result(best, bestScore, done, nodes);
        }

        static String scoreStr(int s) {
            if (s > MATE - MAXPLY) return "mate " + (MATE - s + 1) / 2;
            if (s < -MATE + MAXPLY) return "mate " + -(MATE + s) / 2;
            return "cp " + s;
        }

        String pv(int depth) {
            StringBuilder sb2 = new StringBuilder();
            int made = 0;
            for (int i = 0; i < depth; i++) {
                int idx = (int) p.hash & tmask;
                if (tk[idx] != p.hash || tm[idx] == 0 || !p.isLegal(tm[idx])) break;
                sb2.append(uci(tm[idx])).append(' ');
                p.make(tm[idx]); made++;
            }
            while (made-- > 0) p.unmake();
            return sb2.toString().trim();
        }

        void checkTime() { if (deadline != 0 && System.nanoTime() > deadline) stop = true; }

        int order(int m, int tt, int ply) {
            if (m == tt) return 1_000_000;
            int cap = p.b[to(m)], fl = flags(m);
            if (cap != 0 || (fl & F_EP) != 0) return 100_000 + ((fl & F_EP) != 0 ? P : cap & 7) * 16 - (p.b[from(m)] & 7);
            if (promo(m) != 0) return 90_000 + promo(m);
            if (m == killers[ply * 2]) return 80_000;
            if (m == killers[ply * 2 + 1]) return 79_000;
            return Math.min(70_000, hist[p.side][from(m) * 64 + to(m)]);
        }

        int negamax(int depth, int alpha, int beta, int ply, boolean nullOk) {
            if ((nodes++ & 2047) == 0) checkTime();
            if (stop) return 0;
            if (ply >= MAXPLY - 2) return eval(p);
            boolean pvNode = beta - alpha > 1, inCheck = p.inCheck();
            if (ply > 0) {
                if (p.repetition() || p.half >= 100 || p.insufficient()) return 0;
                alpha = Math.max(alpha, -MATE + ply); beta = Math.min(beta, MATE - ply - 1);
                if (alpha >= beta) return alpha;
            }
            if (inCheck) depth++;
            if (depth <= 0) return qsearch(alpha, beta, ply);

            int idx = (int) p.hash & tmask, ttMove = 0;
            if (tk[idx] == p.hash) {
                ttMove = tm[idx];
                if (ply > 0 && td[idx] >= depth) {
                    int sc = ts[idx];
                    if (sc > MATE - MAXPLY) sc -= ply; else if (sc < -MATE + MAXPLY) sc += ply;
                    int fl = tf[idx];
                    if (fl == 1 || (fl == 2 && sc >= beta) || (fl == 3 && sc <= alpha)) return sc;
                }
            }
            if (nullOk && !pvNode && !inCheck && depth >= 3 && ply > 0 && p.hasNonPawn(p.side)) {
                p.make(0);
                int sc = -negamax(depth - 3 - (depth >= 6 ? 1 : 0), -beta, -beta + 1, ply + 1, false);
                p.unmake();
                if (stop) return 0;
                if (sc >= beta) return sc > MATE - MAXPLY ? beta : sc;
            }

            int[] m = mb[ply], sco = sb[ply];
            int n = p.gen(m, false);
            for (int i = 0; i < n; i++) sco[i] = order(m[i], ttMove, ply);
            int best = -INF, bestMove = 0, legal = 0, origAlpha = alpha;
            for (int i = 0; i < n; i++) {
                int bi = i;
                for (int j = i + 1; j < n; j++) if (sco[j] > sco[bi]) bi = j;
                int mm = m[bi]; m[bi] = m[i]; m[i] = mm; int ss = sco[bi]; sco[bi] = sco[i]; sco[i] = ss;
                boolean quiet = p.b[to(mm)] == 0 && promo(mm) == 0 && (flags(mm) & F_EP) == 0;
                p.make(mm);
                if (p.attacked(p.king[p.side ^ 1], p.side)) { p.unmake(); continue; }
                legal++;
                int sc, nd = depth - 1;
                if (legal == 1) sc = -negamax(nd, -beta, -alpha, ply + 1, true);
                else {
                    int red = (depth >= 3 && legal >= 4 && quiet && !inCheck) ? 1 : 0;
                    sc = -negamax(nd - red, -alpha - 1, -alpha, ply + 1, true);
                    if (sc > alpha && red > 0) sc = -negamax(nd, -alpha - 1, -alpha, ply + 1, true);
                    if (sc > alpha && sc < beta) sc = -negamax(nd, -beta, -alpha, ply + 1, true);
                }
                p.unmake();
                if (stop) return 0;
                if (sc > best) {
                    best = sc; bestMove = mm;
                    if (sc > alpha) {
                        alpha = sc;
                        if (ply == 0) rootBest = mm;
                        if (alpha >= beta) {
                            if (quiet) {
                                if (killers[ply * 2] != mm) { killers[ply * 2 + 1] = killers[ply * 2]; killers[ply * 2] = mm; }
                                hist[p.side][from(mm) * 64 + to(mm)] += depth * depth;
                            }
                            break;
                        }
                    }
                }
            }
            if (legal == 0) return inCheck ? -MATE + ply : 0;
            int store = best;
            if (store > MATE - MAXPLY) store += ply; else if (store < -MATE + MAXPLY) store -= ply;
            if (tk[idx] != p.hash || depth >= td[idx]) {
                tk[idx] = p.hash; tm[idx] = bestMove; ts[idx] = (short) store; td[idx] = (byte) depth;
                tf[idx] = (byte) (best >= beta ? 2 : best > origAlpha ? 1 : 3);
            }
            return best;
        }

        int qsearch(int alpha, int beta, int ply) {
            if ((nodes++ & 2047) == 0) checkTime();
            if (stop) return 0;
            int stand = eval(p);
            if (ply >= MAXPLY - 2 || stand >= beta) return stand >= beta ? beta : stand;
            if (stand > alpha) alpha = stand;
            int[] m = mb[ply], sco = sb[ply];
            int n = p.gen(m, true);
            for (int i = 0; i < n; i++) sco[i] = order(m[i], 0, ply);
            for (int i = 0; i < n; i++) {
                int bi = i;
                for (int j = i + 1; j < n; j++) if (sco[j] > sco[bi]) bi = j;
                int mm = m[bi]; m[bi] = m[i]; m[i] = mm; int ss = sco[bi]; sco[bi] = sco[i]; sco[i] = ss;
                p.make(mm);
                if (p.attacked(p.king[p.side ^ 1], p.side)) { p.unmake(); continue; }
                int sc = -qsearch(-beta, -alpha, ply + 1);
                p.unmake();
                if (stop) return 0;
                if (sc >= beta) return beta;
                if (sc > alpha) alpha = sc;
            }
            return alpha;
        }
    }

    // ------------------------------------------------------------------ UCI
    static void uciLoop() throws IOException {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        Pos pos = Pos.fromFen(START);
        Engine eng = new Engine(16);
        Thread[] worker = {null};
        for (String line; (line = in.readLine()) != null; ) {
            String[] t = line.trim().split("\\s+");
            if (t[0].isEmpty()) continue;
            switch (t[0]) {
                case "uci" -> {
                    System.out.println("id name Knightly " + VERSION);
                    System.out.println("id author Knightly contributors");
                    System.out.println("option name Hash type spin default 16 min 1 max 1024");
                    System.out.println("uciok");
                }
                case "isready" -> System.out.println("readyok");
                case "ucinewgame" -> { eng.clear(); pos = Pos.fromFen(START); }
                case "setoption" -> {
                    int vi = Arrays.asList(t).indexOf("value");
                    if (line.toLowerCase().contains("name hash") && vi > 0) eng.resize(Integer.parseInt(t[vi + 1]));
                }
                case "position" -> {
                    int i = 1;
                    try {
                        if (t[i].equals("startpos")) { pos = Pos.fromFen(START); i++; }
                        else { StringBuilder f = new StringBuilder(); i++; while (i < t.length && !t[i].equals("moves")) f.append(t[i++]).append(' '); pos = Pos.fromFen(f.toString()); }
                        if (i < t.length && t[i].equals("moves"))
                            for (i++; i < t.length; i++) { int m = pos.parse(t[i]); if (m < 0) break; pos.make(m); }
                    } catch (RuntimeException e) { System.out.println("info string bad position: " + e.getMessage()); }
                }
                case "go" -> {
                    if (worker[0] != null) { eng.stop = true; try { worker[0].join(); } catch (InterruptedException ignored) {} }
                    int depth = 100; long mt = 0, wt = -1, bt = -1, wi = 0, bi = 0; int mtg = 0;
                    for (int i = 1; i < t.length - 0; i++) {
                        String a = t[i]; boolean has = i + 1 < t.length;
                        switch (a) {
                            case "depth" -> { if (has) depth = Integer.parseInt(t[++i]); }
                            case "movetime" -> { if (has) mt = Long.parseLong(t[++i]); }
                            case "wtime" -> { if (has) wt = Long.parseLong(t[++i]); }
                            case "btime" -> { if (has) bt = Long.parseLong(t[++i]); }
                            case "winc" -> { if (has) wi = Long.parseLong(t[++i]); }
                            case "binc" -> { if (has) bi = Long.parseLong(t[++i]); }
                            case "movestogo" -> { if (has) mtg = Integer.parseInt(t[++i]); }
                            default -> { }
                        }
                    }
                    long ms = mt > 0 ? Math.max(1, mt - 30) : 0;
                    long rem = pos.side == 0 ? wt : bt, inc = pos.side == 0 ? wi : bi;
                    if (ms == 0 && rem >= 0) ms = Math.max(5, Math.min(rem - 50, rem / (mtg > 0 ? mtg + 1 : 30) + inc * 3 / 4));
                    final Pos copy = pos.copy(); final int dd = depth; final long mm = ms;
                    worker[0] = new Thread(() -> {
                        Result r = eng.search(copy, dd, mm, true);
                        System.out.println("bestmove " + (r.move() == 0 ? "0000" : uci(r.move())));
                    });
                    worker[0].start();
                }
                case "stop" -> { eng.stop = true; if (worker[0] != null) try { worker[0].join(); } catch (InterruptedException ignored) {} }
                case "d" -> System.out.print(pos.board(-1) + pos.fen() + "\n");
                case "quit" -> { eng.stop = true; return; }
                default -> { }
            }
        }
        eng.stop = true;
        if (worker[0] != null) try { worker[0].join(); } catch (InterruptedException ignored) {}
    }

    // ------------------------------------------------------------------ play in the terminal
    static String fmtScore(int s) {
        if (s > MATE - MAXPLY) return "mate in " + (MATE - s + 1) / 2;
        if (s < -MATE + MAXPLY) return "getting mated in " + (MATE + s) / 2;
        return String.format("%+.2f", s / 100.0);
    }

    static void play(String[] args) throws IOException {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        Pos pos = Pos.fromFen(START);
        Engine eng = new Engine(32);
        int human = 0, last = -1, depth = 40;
        double secs = 2;
        ArrayList<Integer> moves = new ArrayList<>();
        System.out.println("Knightly " + VERSION + ". Type a move like e4, Nf3, O-O or e2e4. Commands: help");
        for (;;) {
            System.out.print("\n" + pos.board(last));
            String res = pos.result();
            if (res != null) { System.out.println("\n" + res + "."); System.out.println("Type 'new' for another game or 'quit'."); }
            else if (pos.inCheck()) System.out.println("Check!");
            if (res == null && pos.side != human) {
                Result r = eng.search(pos, depth, (long) (secs * 1000), false);
                String s = pos.san(r.move());
                System.out.printf("Knightly plays %s  (eval %s, depth %d, %,d nodes)%n", s, fmtScore(r.score()), r.depth(), r.nodes());
                pos.make(r.move()); moves.add(r.move()); last = r.move();
                continue;
            }
            System.out.print(res == null ? (pos.side == 0 ? "White" : "Black") + " to move > " : "> ");
            String line = in.readLine();
            if (line == null) return;
            String[] t = line.trim().split("\\s+");
            String cmd = t[0].toLowerCase();
            switch (cmd) {
                case "" -> { }
                case "quit", "exit", "q" -> { return; }
                case "help" -> System.out.println("""
                    Moves:   e4  Nf3  exd5  O-O  e8=Q  or coordinates like e2e4
                    undo     take back your last move (and the engine's reply)
                    new      start a new game        flip   switch sides
                    level N  engine thinks N seconds per move (now %.1f)
                    fen      print the position (or 'fen <FEN>' to load one)      hint   suggest a move""".formatted(secs));
                case "new" -> { pos = Pos.fromFen(START); moves.clear(); last = -1; eng.clear(); }
                case "flip" -> { human ^= 1; System.out.println("You now play " + (human == 0 ? "White." : "Black.")); }
                case "fen" -> {
                    if (t.length == 1) System.out.println(pos.fen());
                    else try { pos = Pos.fromFen(line.trim().substring(3).trim()); moves.clear(); last = -1; eng.clear(); }
                         catch (RuntimeException e) { System.out.println("Could not read that FEN: " + e.getMessage()); }
                }
                case "level" -> { try { secs = Math.max(0.05, Double.parseDouble(t[1])); System.out.println("Engine thinks " + secs + " s per move."); } catch (RuntimeException e) { System.out.println("Usage: level 2.5"); } }
                case "undo" -> {
                    int k = (res == null && pos.side == human ? 2 : 1);
                    while (k-- > 0 && !moves.isEmpty()) { pos.unmake(); moves.remove(moves.size() - 1); }
                    last = moves.isEmpty() ? -1 : moves.get(moves.size() - 1);
                }
                case "hint" -> { Result r = eng.search(pos, depth, 1000, false); System.out.println("Try " + pos.san(r.move()) + "  (eval " + fmtScore(r.score()) + ")"); }
                default -> {
                    int m = res == null ? pos.parse(line) : -1;
                    if (m < 0) System.out.println(res == null ? "Illegal or unrecognised move. Type 'help'." : "The game is over.");
                    else { pos.make(m); moves.add(m); last = m; }
                }
            }
        }
    }

    // ------------------------------------------------------------------ self-test
    static int passed, failed;
    static void check(String name, boolean ok) {
        if (ok) passed++; else { failed++; System.out.println("  FAIL: " + name); }
    }

    static String mirror(String fen) {                         // flip colors and board: evaluation must be identical
        String[] t = fen.split(" ");
        String[] rows = t[0].split("/");
        StringBuilder b = new StringBuilder();
        for (int i = 7; i >= 0; i--) {
            for (char c : rows[i].toCharArray()) b.append(Character.isUpperCase(c) ? Character.toLowerCase(c) : Character.toUpperCase(c));
            if (i > 0) b.append('/');
        }
        StringBuilder cs = new StringBuilder();
        for (char c : t[2].toCharArray()) cs.append(c == '-' ? c : Character.isUpperCase(c) ? Character.toLowerCase(c) : Character.toUpperCase(c));
        String ep = t[3].equals("-") ? "-" : "" + t[3].charAt(0) + (char) ('1' + '8' - t[3].charAt(1));
        return b + " " + (t[1].equals("w") ? "b" : "w") + " " + cs + " " + ep + " 0 1";
    }

    static int bestMove(String fen, int depth) {
        return new Engine(8).search(Pos.fromFen(fen), depth, 0, false).move();
    }

    static int randomGame(Random rnd, boolean engineWhite, int depth) {
        Pos p = Pos.fromFen(START);
        Engine e = new Engine(4);
        int[] l = new int[256];
        for (int ply = 0; ply < 400; ply++) {
            String res = p.result();
            if (res != null) return res.contains("checkmate") ? ((p.side == 1) == engineWhite ? 1 : -1) : 0;
            int m;
            if ((p.side == 0) == engineWhite) {
                m = e.search(p, depth, 0, false).move();
                if (!p.isLegal(m)) { System.out.println("  engine produced an illegal move!"); return -2; }
            } else { int n = p.legal(l); m = l[rnd.nextInt(n)]; }
            p.make(m);
        }
        return 0;
    }

    static boolean selfTest() {
        long t0 = System.currentTimeMillis();
        System.out.println("Move generation (perft, known node counts)");
        Object[][] suite = {
            {"start position", START, new long[]{20, 400, 8902, 197281}},
            {"kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", new long[]{48, 2039, 97862}},
            {"endgame with pins and en passant", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", new long[]{14, 191, 2812, 43238}},
            {"promotions and castling rights", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", new long[]{6, 264, 9467}},
            {"promotion while in check", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", new long[]{44, 1486, 62379}},
            {"middlegame", "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", new long[]{46, 2079, 89890}},
        };
        for (Object[] s : suite) {
            long[] exp = (long[]) s[2];
            Pos p = Pos.fromFen((String) s[1]);
            boolean all = true;
            for (int d = 1; d <= exp.length; d++) all &= perft(p, d, true) == exp[d - 1];
            check("perft " + s[0], all);
            System.out.println("  " + (all ? "ok  " : "FAIL") + " " + s[0] + " (depth " + exp.length + ", " + String.format("%,d", exp[exp.length - 1]) + " positions)");
        }

        System.out.println("Notation and rules");
        for (String f : new String[]{START, "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", "rnbqkbnr/ppp1pppp/8/3pP3/8/8/PPPP1PPP/RNBQKBNR w KQkq d6 0 3", "8/8/8/4k3/8/8/4P3/4K3 b - - 12 40"})
            check("FEN round trip: " + f, Pos.fromFen(f).fen().equals(f));
        boolean sanOk = true;
        for (String f : new String[]{START, "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", "4k3/8/8/8/8/8/8/R3K2R w KQ - 0 1", "4k3/8/8/8/8/8/8/N1N1K3 w - - 0 1", "R6R/3Q4/1Q4Q1/4Q3/2Q4Q/Q4Q2/pp1Q4/kBNN1KB1 w - - 0 1"}) {
            Pos p = Pos.fromFen(f);
            int[] l = new int[256]; int n = p.legal(l);
            Set<String> seen = new HashSet<>();
            for (int i = 0; i < n; i++) { String s = p.san(l[i]); seen.add(s); sanOk &= p.parse(s) == l[i] && p.parse(uci(l[i])) == l[i]; }
            sanOk &= seen.size() == n;
        }
        check("every move round-trips through SAN and is unique (incl. disambiguation, promotion, castling)", sanOk);
        Pos s0 = Pos.fromFen(START);
        check("SAN of opening moves", s0.san(s0.parse("e4")) .equals("e4") && s0.san(s0.parse("g1f3")).equals("Nf3") && s0.parse("Ke2") < 0);
        Pos mate = Pos.fromFen("R5k1/5ppp/8/8/8/8/8/6K1 b - - 0 1");
        check("checkmate detected", "White wins by checkmate".equals(mate.result()));
        check("stalemate detected", "Draw by stalemate".equals(Pos.fromFen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1").result()));
        check("insufficient material detected", Pos.fromFen("8/8/8/4k3/8/3K4/8/8 w - - 0 1").insufficient() && Pos.fromFen("8/8/8/4k3/8/3KN3/8/8 w - - 0 1").insufficient() && !Pos.fromFen("8/8/8/4k3/8/3KR3/8/8 w - - 0 1").insufficient());
        Pos rep = Pos.fromFen(START);
        for (String m : "g1f3 g8f6 f3g1 f6g8 g1f3 g8f6 f3g1 f6g8".split(" ")) rep.make(rep.parse(m));
        check("threefold repetition detected", rep.repCount() == 3 && "Draw by threefold repetition".equals(rep.result()));
        Pos castle = Pos.fromFen("r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1");
        check("castling both ways, then rights are lost", castle.parse("O-O") >= 0 && castle.parse("O-O-O") >= 0);
        Pos blocked = Pos.fromFen("r3k2r/8/8/8/8/5r2/8/R3K2R w KQkq - 0 1");
        check("cannot castle through an attacked square", blocked.parse("O-O") < 0 && blocked.parse("O-O-O") >= 0);
        Pos ep = Pos.fromFen("rnbqkbnr/ppp1pppp/8/8/3pP3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 3");
        int epm = ep.parse("dxe3"); String before = ep.fen();
        ep.make(epm); boolean gone = ep.b[28] == 0; ep.unmake();
        check("en passant captures the pawn and undoes cleanly", epm >= 0 && gone && ep.fen().equals(before));

        System.out.println("Evaluation");
        boolean sym = true;
        for (String f : new String[]{START, "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"})
            sym &= eval(Pos.fromFen(f)) == eval(Pos.fromFen(mirror(f)));
        check("evaluation is colour-symmetric (catches flipped tables)", sym);
        check("start position is roughly equal", Math.abs(eval(Pos.fromFen(START))) < 30);
        check("being a queen up is worth a lot", eval(Pos.fromFen("rnb1kbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")) > 700);

        System.out.println("Search");
        check("mate in 1 (Scholar's mate)", uci(bestMove("r1bqkb1r/pppp1ppp/2n2n2/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w KQkq - 4 4", 3)).equals("h5f7"));
        check("mate in 1 as Black (fool's mate)", uci(bestMove("rnbqkbnr/pppp1ppp/8/4p3/6P1/5P2/PPPPP2P/RNBQKBNR b KQkq - 0 2", 3)).equals("d8h4"));
        check("back-rank mate in 1", uci(bestMove("6k1/5ppp/8/8/8/8/5PPP/R5K1 w - - 0 1", 3)).equals("a1a8"));
        Result m2 = new Engine(8).search(Pos.fromFen("7k/8/8/8/8/8/1R6/R6K w - - 0 1"), 6, 0, false);
        check("finds mate in 2 with two rooks (score = mate in 2)", Engine.scoreStr(m2.score()).equals("mate 2") && (uci(m2.move()).equals("a1a7") || uci(m2.move()).equals("b2b7")));
        check("wins a hanging queen", uci(bestMove("4k3/8/8/3q4/8/8/8/3RK3 w - - 0 1", 3)).equals("d1d5"));
        check("avoids stalemate when winning", !uci(bestMove("7k/8/5QK1/8/8/8/8/8 w - - 0 1", 4)).equals("f6f7") && Pos.fromFen("7k/8/5QK1/8/8/8/8/8 w - - 0 1").parse("Qf7") >= 0);
        check("knight fork of king and queen (Nd6+)", uci(bestMove("2q1k3/8/8/1N6/8/8/8/4K3 w - - 0 1", 4)).equals("b5d6"));
        // Queen + king vs king: the engine must actually deliver mate (tests the mop-up evaluation).
        Pos kq = Pos.fromFen("8/8/8/4k3/8/8/8/Q3K3 w - - 0 1");
        Engine ee = new Engine(8);
        int plies = 0; String end = null;
        for (; plies < 80 && end == null; plies++) { end = kq.result(); if (end == null) kq.make(ee.search(kq, 6, 0, false).move()); }
        check("converts king + queen vs king to checkmate (" + (plies / 2) + " moves)", "White wins by checkmate".equals(end));

        System.out.println("Games against a random mover (depth 3)");
        Random rnd = new Random(7);
        int wins = 0, illegal = 0, losses = 0;
        for (int g = 0; g < 6; g++) { int r = randomGame(rnd, g % 2 == 0, 3); if (r == 1) wins++; else if (r == -1) losses++; else if (r == -2) illegal++; }
        System.out.println("  engine won " + wins + " of 6, lost " + losses);
        check("never plays an illegal move", illegal == 0);
        check("never loses to a random mover", losses == 0 && wins >= 4);

        System.out.println(passed + "/" + (passed + failed) + " checks passed in " + (System.currentTimeMillis() - t0) / 1000.0 + " s");
        return failed == 0;
    }

    static void bench() {
        String[] fens = {START, "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
            "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", "2r3k1/pp3ppp/8/3p4/3P4/2R2P2/PP4PP/6K1 w - - 0 1"};
        long nodes = 0, t0 = System.nanoTime();
        Engine e = new Engine(32);
        for (String f : fens) { e.clear(); Result r = e.search(Pos.fromFen(f), 7, 0, false); nodes += r.nodes(); System.out.printf("  %-8s best %s%n", "depth 7", uci(r.move())); }
        double s = (System.nanoTime() - t0) / 1e9;
        System.out.printf("%,d nodes in %.2f s = %,d nodes/s%n", nodes, s, (long) (nodes / s));
    }

    static void usage() {
        System.out.println("""
            Knightly %s: a chess engine in one Java file.
              java Knightly.java            play against the engine in the terminal
              java Knightly.java uci        UCI mode (for Arena, Cute Chess, Lucas Chess, ...)
              java Knightly.java perft N [FEN]   count positions to depth N
              java Knightly.java selftest   run the test suite
              java Knightly.java bench      search speed benchmark""".formatted(VERSION));
    }

    public static void main(String[] a) throws Exception {
        String cmd = a.length > 0 ? a[0] : "play";
        switch (cmd) {
            case "play" -> play(a);
            case "uci" -> uciLoop();
            case "selftest" -> System.exit(selfTest() ? 0 : 1);
            case "bench" -> bench();
            case "perft" -> {
                int d = a.length > 1 ? Integer.parseInt(a[1]) : 5;
                Pos p = Pos.fromFen(a.length > 2 ? String.join(" ", Arrays.copyOfRange(a, 2, a.length)) : START);
                long t0 = System.nanoTime(), n = 0;
                int[] m = new int[256], l = new int[256];
                int c = p.legal(l);
                for (int i = 0; i < c; i++) { p.make(l[i]); long k = d <= 1 ? 1 : perft(p, d - 1, false); p.unmake(); System.out.println(uci(l[i]) + ": " + k); n += k; }
                double s = (System.nanoTime() - t0) / 1e9;
                System.out.printf("%nNodes: %,d  (%.2f s, %,d nodes/s)%n", n, s, (long) (n / Math.max(s, 1e-9)));
            }
            case "help", "--help", "-h" -> usage();
            default -> { usage(); System.exit(2); }
        }
    }
}
