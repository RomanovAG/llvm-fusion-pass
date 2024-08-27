#include <stdio.h>

int max(int a, int b)
{
	return a >= b ? a : b;
}

void print_2d_arr(int A[][100], int N)
{
	for (int i = 0; i < N; i++)
	{
		for (int j = 0; j < N; j++)
		{
			printf("%d", A[i][j]);
		}
	}
	printf("\n");
}

void to_be_fused(int N, int M)
{
	int arr[66] = {0};
	//printf("Func begin\n");
	for ( int i = 0; i < N; i++)
	{
		//printf("Loop 1 begin\n");
		for (int j = 0; j < M; j++)
		{
			//printf("\tLoop 1.1\n");
		}
		//printf("Loop 1 end\n");
	}
	//printf("Func middle\n");
	int a = 0;
	for (int k = 0; k < N; k++)
	{
		//a = printf("Loop 2 begin\n");
		for (int l = 0; l < M; l++)
		{
			//a = printf("\tLoop 2.1\n");
			arr[M]++;
			a++;
		}
		a = max(a, arr[5]);
		//printf("Loop 2 middle %d\n", a);
		for (int l = 0; l < M; l++)
		{
			a--;
			//printf("\tLoop 2.2\n");
		}
		//printf("Loop 2 end\n");
	}
	printf("Func end %d\n", a);
}

void doit1_should(int *a, size_t n)
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

void simple_1_should(int *A, int *B, int SIZE)
{
	for (int i = 0; i < SIZE; i++)
	{
		A[i] = i;
	}
	for (int i = 0; i < SIZE; i++)
	{
		B[i] = A[i] + 1;
	}
}

void nested_no_dep_should(int F[][100], int G[][100], int SIZE)
{
	for (int i = 0; i < SIZE; i++)
	{
		for (int j = 0; j < SIZE; j++)
		{
			F[i][j] = i * j;
			//printf("case 2 loop 1.1");
		}
	}
	for (int i = 0; i < SIZE; i++)
	{
		for (int j = 0; j < SIZE; j++)
		{
			G[j][i]++;
		}
	}
}

void diff_directions_shouldnot(int *a, int *b, int N)
{
	for (int i = 0; i < N; i++)
	{
		a[i] *= 3;
		a[i]--;
	}
	for (int i = N - 1; i >= 0; i--)
	{
		b[i] = a[i];
	}
}

void diff_directions_var2_shouldnot(int *a, int *b, int N)
{
	for (int i = 0; i < N; i++)
	{
		a[i] *= 3;
	}
	for (int i = 0; i < N; i++)
	{
		b[N - i - 1] = a[N - i - 1];
	}
}

void ambiguous_dependence_shouldnot(int *A, int *B, int SIZE)
{
	for (int i = 1; i < SIZE; i++)
	{
		A[i] = A[i - 1] + 1;
	}
	for (int i = 0; i < SIZE; i++)
	{
		B[i] = A[i] * 2;
	}
}

void multiple_entries_exits_shouldnot(int N)
{
	for (int i = 0; i < N; i += 2)
	{
		if (i == 6)
			goto a;
	}
	for (int i = 0; i < N; i += 2)
	{
	}
	for (int i = 0; i < N; i += 2)
	{
		a:
		printf("mee 3");
	}
}

void sum_reduction_should(int *A, int *B, int N)
{
	int i;
	int sum = 0;
	for (i = 0; i < N; i++)
	{
		sum += A[i];
	}
	int dec = -1;
	for (i = 0; i < N; i++)
	{
		sum += B[i];
		sum += 2;
		dec -= 3;
	}
	for (i = 0; i < N; i++)
	{
		dec -= 1;
	}
	for (i = 0; i < N; i++)
	{
		sum += 1;
	}

	printf("sum_reduction: sum(%d), dec(%d)\n", sum, dec);
}

void extreme_test(int SIZE) 
{
    int A[SIZE], B[SIZE], C[SIZE], D[SIZE];
    int E[100] = {0};
    int F[SIZE][SIZE], G[SIZE][SIZE], H[SIZE][SIZE], I[SIZE][SIZE];
    int i, j, k;
	if (SIZE == 100)
	{
		for (i = 0; i < SIZE; i++)
		{
			A[i] = i;
			B[i] = i*2;
			C[i] = i*3;
			D[i] = i*4;
			E[i] = i*5;
			for (j = 0; j < SIZE; j++)
			{
				F[i][j] = i + j;
				G[i][j] = i - j;
				H[i][j] = i * j;
				I[i][j] = i / max(j, 1);
			}
		}
	}
	to_be_fused(50, 66);
	
	for (i = 1; i < SIZE; i++)
	{
		A[i] = A[i - 1] + 1;
	}
	for (i = 0; i < SIZE; i++)
	{
		B[i] = A[i] * 2;
	}
	nested_no_dep_should(F, G, SIZE);
	print_2d_arr(F, SIZE);
	print_2d_arr(G, SIZE);

	// Loops with different strides
	for (i = 0; i < SIZE; i += 2)
	{
		C[i]++;
	}
	for (i = 1; i < SIZE; i += 2)
	{
		D[i]--;
	}

	diff_directions_shouldnot(A, B, SIZE);

	// Loops with complex control flow
	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++)
		{
			if (i % 2 == 0)
			{
				H[i][j] = H[i][j] + i + j;
			} 
			else
			{
				H[i][j] = H[j][i] - i - j;
			}
		}
	}
	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++)
		{
			if (H[i][j] > 0)
			{
				I[i][j] = H[j][i] * 2;
			}
			else
			{
				I[i][j] = H[i][j] / 2;
			}
		}
	}

	// Nested loops with dependencies on different levels
	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++)
		{
			E[i] = i + j;
		}
		for (j = 0; j < SIZE; j++)
		{
			E[i] += E[j] + (i - j);
		}
	}
	
	diff_directions_var2_shouldnot(A, B, SIZE);

	for (int i = 0; i < SIZE; i++)
	{
		for (int j = 0; j < SIZE; j++)
		{
			F[i][j] = i * j;
		}
	}
	for (int i = 0; i < SIZE; i++)
	{
		for (int j = 0; j < SIZE; j++)
		{
			G[i][j] += 1 + (i / max(j, 1));
		}
	}

	printf("A[12] = %d, B[23] = %d, C[34] = %d, D[45] = %d, E[56] = %d\n", A[12], B[23], C[34], D[45], E[56]);
	printf("F[11][22] = %d, G[33][44] = %d, H[55][66] = %d, I[77][88] = %d", F[11][22], G[33][44], H[55][66], I[77][88]);
	for (i = 0; i < SIZE; i++)
	{
		printf("A[%d] = %d; ", i, A[i]);
		printf("B[%d] = %d; ", i, B[i]);
		printf("C[%d] = %d; ", i, C[i]);
		printf("D[%d] = %d; ", i, D[i]);
		printf("E[%d] = %d;\n", i, E[i]);
		for (j = 0; j < SIZE; j++)
		{
			printf("F[%d][%d] = %d; ", i, j, F[i][j]);
			printf("G[%d][%d] = %d; ", i, j, G[i][j]);
			printf("H[%d][%d] = %d; ", i, j, H[i][j]);
			printf("I[%d][%d] = %d;\n", i, j, I[i][j]);
		}
	}
}

int main()
{
	int N = 100;
	int A[N], B[N];
	for (int i = 0; i < N; i++)
	{
		A[i] = i;
		B[i] = i * 2 - 1;
	}
	sum_reduction_should(A, B, N);
	extreme_test(100);
	return 0;
}

