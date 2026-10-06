/* col3: read graph6 (n<=30) from stdin; write to stdout every graph that is NOT 3-colourable.
   stderr: "read=<N> not3col=<M>".
   Exact search: backtracking, always branching on an uncoloured vertex with the fewest
   admissible colours (most coloured neighbours as tie-break); a new colour class may only
   be opened in increasing order (colour symmetry breaking). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int n;
static uint32_t adj[32];
static uint32_t cls[3];   /* vertices in each colour class */

static int search(uint32_t uncol, int used)
{
    if (!uncol) return 1;
    int best = -1, bestcnt = 4; uint32_t bestmask = 0;
    for (uint32_t u = uncol; u; u &= u - 1) {
        int v = __builtin_ctz(u);
        uint32_t m = 0; int cnt = 0;
        for (int c = 0; c < 3; c++)
            if (!(adj[v] & cls[c])) { m |= 1u << c; cnt++; }
        if (cnt == 0) return 0;
        if (cnt < bestcnt) { bestcnt = cnt; best = v; bestmask = m; if (cnt == 1) break; }
    }
    uint32_t bit = 1u << best;
    int lim = used < 3 ? used + 1 : 3;   /* colours 0..lim-1 allowed */
    for (int c = 0; c < lim; c++) {
        if (!(bestmask >> c & 1)) continue;
        cls[c] |= bit;
        int r = search(uncol & ~bit, (c == used) ? used + 1 : used);
        cls[c] &= ~bit;
        if (r) return 1;
    }
    return 0;
}

int main(void)
{
    static char line[4096];
    unsigned long long nread = 0, nbad = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' ) continue;           /* header, if any */
        size_t len = strcspn(line, "\r\n");
        if (len == 0) continue;
        n = line[0] - 63;
        if (n < 0 || n > 30) { fprintf(stderr, "bad n\n"); return 2; }
        size_t need = 1 + ((size_t)n * (n - 1) / 2 + 5) / 6;
        if (len != need) { fprintf(stderr, "bad line length\n"); return 2; }
        memset(adj, 0, sizeof adj);
        int k = 0;
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++, k++) {
                int byte = line[1 + k / 6] - 63;
                if (byte < 0 || byte > 63) { fprintf(stderr, "bad char\n"); return 2; }
                if (byte >> (5 - k % 6) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            }
        nread++;
        cls[0] = cls[1] = cls[2] = 0;
        uint32_t all = (n == 32) ? ~0u : ((1u << n) - 1);
        if (!search(all, 0)) { nbad++; line[len] = 0; puts(line); }
    }
    fprintf(stderr, "read=%llu not3col=%llu\n", nread, nbad);
    return 0;
}
