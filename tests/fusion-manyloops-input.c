#include <stdio.h>

int max(int a, int b)
{
	return a >= b ? a : b;
}

void toBeFused(int N, int M)
{
	printf("Func begin\n");
	for ( int i = 0; i < N; i++)
	{
		printf("Loop 1 begin\n");
		for (int j = 0; j < M; j++)
		{
			printf("\tLoop 1.1\n");
		}
		printf("Loop 1 end\n");
	}
	printf("Func middle\n");
	for (int k = 0; k < N; k++)
	{
		int a = printf("Loop 2 begin\n");
		for (int l = 0; l < M; l++)
		{
			a = printf("\tLoop 2.1\n");
		}
		a = max(a, 1);
		printf("Loop 2 middle %d\n", a);
		for (int l = 0; l < M; l++)
		{
			printf("\tLoop 2.2\n");
		}
		printf("Loop 2 end\n");
	}
	printf("Func end\n");
}

void doit1(int *a, size_t n)
{
	for (size_t i = 0; i < n; i++)
	{
		a[i] = a[i] + 3;
	}
	for (size_t i = 0; i < n; i++)
	{
		a[i] = a[i] * 5;
	}
	for (size_t i = 0; i < n; i++)
	{
		a[i] = a[i] - 23;
	}
	for (size_t i = 0; i < n; i++)
	{
		a[i] = (a[i] >> 10) & 0xFF;
	}
}

void doit2(int *a, size_t n)
{
	for (size_t i = 0; i < n; i++)
	{
		a[i] = a[i] + 3;
		a[i] = a[i] * 5;
		a[i] = a[i] - 23;
		a[i] = (a[i] >> 10) & 0xFF;
	}
}

void diff_directions(int *a, int *b, int N)
{
	for (int i = 0; i < N; i++)
	{
		a[i] = i;
	}
	for (int i = N - 1; i >= 0; i--)
	{
		b[i] = a[i];
	}
}

void sum_reduction(int *A, int *B, int N)
{
	int i;
	int sum = 0;
	for (i = 0; i < N; i++)
	{
		sum += A[i];
	}
	for (i = 0; i < N; i++)
	{
		sum += B[i];
	}
}

void extreme_test(int SIZE) 
{
    int A[SIZE], B[SIZE], C[SIZE], D[SIZE], E[SIZE];
    int F[SIZE][SIZE], G[SIZE][SIZE], H[SIZE][SIZE], I[SIZE][SIZE];
    int i, j, k, sum = 0;
    if (SIZE == 100)
	{
		for (i = 0; i < SIZE; i++)
		{
			A[i] = i;
			B[i] = i*2;
			B[i] = i*3;
			B[i] = i*4;
			E[i] = i*5;
		}
	}

    // Case 1: Simple consecutive loops that can be fused
    for (i = 0; i < SIZE; i++) {
        A[i] = i;
    }
    for (i = 0; i < SIZE; i++) {
        B[i] = A[i] + 1;
    }

    // Case 2: Nested loops with no dependencies
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++) {
            F[i][j] = i * j;
	    //printf("case 2 loop 1.1");
        }
    }
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++) {
            G[i][j] = F[i][j] + 1;
        }
    }

    // Case 3: Dependent loops that cannot be fused
    for (i = 1; i < SIZE; i++) {
        A[i] = A[i - 1] + 1;
    }
    for (i = 0; i < SIZE; i++) {
        B[i] = A[i] * 2;
    }

    // Case 4: Loops with different strides
    for (i = 0; i < SIZE; i += 2) {
        C[i] = i;
    }
    for (i = 1; i < SIZE; i += 2) {
        D[i] = i;
    }

    // Case 5: Loops with complex control flow
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++) {
            if (i % 2 == 0) {
                H[i][j] = i + j;
            } else {
                H[i][j] = i - j;
            }
        }
    }
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++) {
            if (H[i][j] > 0) {
                I[i][j] = H[i][j] * 2;
            } else {
                I[i][j] = H[i][j] / 2;
            }
        }
    }

    // Case 6: Nested loops with dependencies on different levels
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++) {
            E[i] = i + j;
        }
        for (j = 0; j < SIZE; j++) {
            E[i] += E[j];
        }
    }

    // Output some results to prevent optimizations from removing loops
    printf("A[12] = %d, B[23] = %d, C[34] = %d, D[45] = %d, E[56] = %d\n", A[12], B[23], C[34], D[45], E[56]);
    printf("F[1][2] = %d, G[3][4] = %d, H[5][6] = %d, I[7][8] = %d, Sum = %d\n", F[1][2], G[3][4], H[5][6], I[7][8], sum);
}

int main() {
    extreme_test(100);
    return 0;
}

