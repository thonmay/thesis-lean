// Exhaustive check: for a fixed update pattern (insert set I, delete set D) placed on
// vertices 0..k-1 of an n-vertex graph, enumerate every host graph G (D ⊆ G, I ∩ G = ∅)
// and test whether G and G' = (G \ D) ∪ I share an MCS ordering under arbitrary
// tie-breaking.  Common-ordering existence is reachability in the subset lattice,
// because MCS legality of the next pick depends only on the chosen *set*.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static unsigned char reach[1 << 12];

static int common(const unsigned *A, const unsigned *B) {
    int full = (1 << n) - 1;
    memset(reach, 0, (size_t)1 << n);
    reach[0] = 1;
    for (int S = 0; S < full; S++) {
        if (!reach[S]) continue;
        int ca[16], cb[16], MA = -1, MB = -1;
        for (int x = 0; x < n; x++) if (!((S >> x) & 1)) {
            ca[x] = __builtin_popcount(A[x] & S);
            cb[x] = __builtin_popcount(B[x] & S);
            if (ca[x] > MA) MA = ca[x];
            if (cb[x] > MB) MB = cb[x];
        }
        for (int x = 0; x < n; x++)
            if (!((S >> x) & 1) && ca[x] == MA && cb[x] == MB) reach[S | (1 << x)] = 1;
    }
    return reach[full];
}

static int parse(const char *s, int *ei, int *ej) {  // "0-1,2-3" or "-"
    int m = 0;
    if (strcmp(s, "-") == 0) return 0;
    const char *p = s;
    while (*p) {
        int a, b, k;
        if (sscanf(p, "%d-%d%n", &a, &b, &k) != 2) break;
        ei[m] = a; ej[m] = b; m++;
        p += k;
        if (*p == ',') p++;
    }
    return m;
}

static void addE(unsigned *A, int a, int b) { A[a] |= 1u << b; A[b] |= 1u << a; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: n INSERT DELETE [check G-edges]\n"); return 1; }
    n = atoi(argv[1]);
    int Ii[64], Ij[64], Di[64], Dj[64];
    int ni = parse(argv[2], Ii, Ij), nd = parse(argv[3], Di, Dj);
    if (argc >= 6 && strcmp(argv[4], "check") == 0) {   // check one explicit host
        int Gi[64], Gj[64]; int ng = parse(argv[5], Gi, Gj);
        unsigned A[16] = {0}, B[16] = {0};
        for (int e = 0; e < ng; e++) { addE(A, Gi[e], Gj[e]); addE(B, Gi[e], Gj[e]); }
        // G' = (G \ D) ∪ I : rebuild B
        memset(B, 0, sizeof B);
        for (int e = 0; e < ng; e++) {
            int del = 0;
            for (int d = 0; d < nd; d++)
                if ((Di[d] == Gi[e] && Dj[d] == Gj[e]) || (Di[d] == Gj[e] && Dj[d] == Gi[e])) del = 1;
            if (!del) addE(B, Gi[e], Gj[e]);
        }
        for (int e = 0; e < ni; e++) addE(B, Ii[e], Ij[e]);
        printf("common=%d\n", common(A, B));
        return 0;
    }
    // free pairs
    int fi[64], fj[64], nf = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        int used = 0;
        for (int e = 0; e < ni; e++) if ((Ii[e] == a && Ij[e] == b) || (Ii[e] == b && Ij[e] == a)) used = 1;
        for (int e = 0; e < nd; e++) if ((Di[e] == a && Dj[e] == b) || (Di[e] == b && Dj[e] == a)) used = 1;
        if (!used) { fi[nf] = a; fj[nf] = b; nf++; }
    }
    long long fails = 0, total = 0; long long first = -1; int bestEdges = 99; long long best = -1;
    for (long long mask = 0; mask < (1LL << nf); mask++) {
        unsigned A[16] = {0}, B[16] = {0};
        int ec = 0;
        for (int e = 0; e < nf; e++) if ((mask >> e) & 1) { addE(A, fi[e], fj[e]); addE(B, fi[e], fj[e]); ec++; }
        for (int e = 0; e < nd; e++) addE(A, Di[e], Dj[e]);
        for (int e = 0; e < ni; e++) addE(B, Ii[e], Ij[e]);
        total++;
        if (!common(A, B)) {
            fails++;
            if (first < 0) first = mask;
            if (ec < bestEdges) { bestEdges = ec; best = mask; }
        }
    }
    printf("n=%d hosts=%lld fails=%lld", n, total, fails);
    if (best >= 0) {
        printf(" sparsest_host(free edges + D)={");
        for (int e = 0; e < nf; e++) if ((best >> e) & 1) printf("(%d,%d)", fi[e], fj[e]);
        for (int e = 0; e < nd; e++) printf("(%d,%d)", Di[e], Dj[e]);
        printf("}");
    }
    printf("\n");
    return 0;
}

