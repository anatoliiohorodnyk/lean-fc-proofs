/* brute3: independent reference. For each graph6 line (n<=12) print "1" if some map
   V -> {0,1,2} (all 3^n maps enumerated by counting in base 3) is a proper colouring, else "0".
   Graph decoding is written differently (edge list, bit stream consumed sequentially). */
#include <stdio.h>
#include <string.h>

int main(void)
{
    char s[1024];
    while (fgets(s, sizeof s, stdin)) {
        int L = (int)strlen(s);
        while (L > 0 && (s[L-1] == '\n' || s[L-1] == '\r')) s[--L] = 0;
        if (L == 0 || s[0] == '>') continue;
        int nv = s[0] - '?';
        int eu[80], ev[80], ne = 0;
        int pos = 1, bitsleft = 0, cur = 0;
        for (int b = 1; b < nv; b++)
            for (int a = 0; a < b; a++) {
                if (bitsleft == 0) { cur = s[pos++] - '?'; bitsleft = 6; }
                bitsleft--;
                if ((cur >> bitsleft) & 1) { eu[ne] = a; ev[ne] = b; ne++; }
            }
        long total = 1; for (int i = 0; i < nv; i++) total *= 3;
        int found = 0;
        for (long code = 0; code < total && !found; code++) {
            int col[16]; long t = code;
            for (int i = 0; i < nv; i++) { col[i] = (int)(t % 3); t /= 3; }
            int ok = 1;
            for (int e = 0; e < ne; e++) if (col[eu[e]] == col[ev[e]]) { ok = 0; break; }
            found = ok;
        }
        puts(found ? "1" : "0");
    }
    return 0;
}
