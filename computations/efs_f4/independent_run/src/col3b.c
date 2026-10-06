/* col3b: second exact 3-colourability test, written differently from col3:
   adjacency matrix, vertices coloured in fixed order 0..n-1 by recursive backtracking
   (vertex 0 fixed to colour 0, no other pruning). Every colouring found is re-verified
   against the edge list before the graph is accepted as 3-colourable.
   Prints non-3-colourable graphs; stderr: counts. */
#include <stdio.h>
#include <string.h>
static int N, A[32][32], col[32];
static int rec(int v) {
    if (v == N) return 1;
    for (int c = 0; c < (v == 0 ? 1 : 3); c++) {
        int ok = 1;
        for (int u = 0; u < v; u++) if (A[u][v] && col[u] == c) { ok = 0; break; }
        if (!ok) continue;
        col[v] = c;
        if (rec(v + 1)) return 1;
    }
    return 0;
}
int main(void) {
    char s[1024]; unsigned long long rd = 0, bad = 0, verified = 0;
    while (fgets(s, sizeof s, stdin)) {
        if (s[0] == '>' || s[0] == '\n') continue;
        s[strcspn(s, "\r\n")] = 0;
        N = s[0] - 63; memset(A, 0, sizeof A);
        int idx = 0;
        for (int j = 1; j < N; j++) for (int i = 0; i < j; i++, idx++)
            A[i][j] = A[j][i] = ((s[1 + idx / 6] - 63) >> (5 - idx % 6)) & 1;
        rd++;
        if (rec(0)) {
            for (int i = 0; i < N; i++) { if (col[i] < 0 || col[i] > 2) return 3;
                for (int j = i + 1; j < N; j++) if (A[i][j] && col[i] == col[j]) { fprintf(stderr, "INVALID WITNESS\n"); return 3; } }
            verified++;
        } else { bad++; puts(s); }
    }
    fprintf(stderr, "read=%llu witness_verified=%llu not3col=%llu\n", rd, verified, bad);
    return 0;
}
