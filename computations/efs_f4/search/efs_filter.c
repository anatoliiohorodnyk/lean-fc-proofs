/* efs_filter: read graph6 (n <= 32) from stdin; keep graphs whose maximum degree multiplicity
   f is <= FMAX (argv[2], default 3) and that are NOT (k-1)-colourable (k = argv[1]).
   Prints the kept graphs (graph6) to stdout and counts to stderr.
   The input is expected to be triangle-free already (geng -t); this is re-checked. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n; static unsigned adj[32]; static int col[32];
static int colour(int v, int k) {            /* plain backtracking, vertices in input order */
  if (v == n) return 1;
  unsigned used = 0;
  for (int u = 0; u < v; u++) if (adj[v] >> u & 1) used |= 1u << col[u];
  int maxc = 0; for (int u = 0; u < v; u++) if (col[u] + 1 > maxc) maxc = col[u] + 1;
  for (int c = 0; c < k && c <= maxc; c++)   /* symmetry: first use of colours in order */
    if (!(used >> c & 1)) { col[v] = c; if (colour(v + 1, k)) return 1; }
  return 0;
}
int main(int argc, char **argv) {
  int k = atoi(argv[1]); int fmax = argc > 2 ? atoi(argv[2]) : 3;
  char line[256]; long total = 0, fok = 0, kept = 0, tri = 0;
  while (fgets(line, sizeof line, stdin)) {
    n = line[0] - 63; memset(adj, 0, sizeof adj);
    int pos = 1, bit = 5;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
      if ((line[pos] - 63) >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
      if (--bit < 0) { bit = 5; pos++; }
    }
    total++;
    int cnt[33] = {0}, f = 0;
    for (int v = 0; v < n; v++) { int d = __builtin_popcount(adj[v]); if (++cnt[d] > f) f = cnt[d]; }
    if (f > fmax) continue;
    fok++;
    int t = 0;
    for (int v = 0; v < n && !t; v++) for (int u = 0; u < v; u++)
      if ((adj[v] >> u & 1) && (adj[v] & adj[u])) { t = 1; break; }
    if (t) { tri++; continue; }
    if (colour(0, k - 1)) continue;
    kept++; fputs(line, stdout);
  }
  fprintf(stderr, "n=%d total=%ld f<=%d:%ld with-triangle=%ld kept(not %d-colourable)=%ld\n", n, total, fmax, fok, tri, k - 1, kept);
  return 0;
}
