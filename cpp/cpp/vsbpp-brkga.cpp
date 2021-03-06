#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <time.h>
#include <float.h>
#include <string.h>
#include <ctype.h>

#include <map>
#include <random>
#include <vector>
#include <iostream>
using namespace std;

#define MAXINT 0x7fffffff

/* Estrutura criada para a busca tabu manter os dados dos movimentos a serem executados */
typedef struct move_info
{
    double value;
    int i;
    int j;
} move_tabu;

/* Estrutura criada para armazenar os dados contidos no arquivo de configuracao 'config.txt' */
struct config
{
    int pop_size;  /* Size of the population */
    int max_gen;   /* Maximum number of generations to evolve */
    double pe;     /* fraction of population of the elite set in population */
    double pm;     /* fraction of population to be replaced by mutants */
    double rhoe;   /* probability that offspring inherit an allele from elite parent */
    int tabu_size; /* number of iterations tabu */
    int max_iter;  /* maximum number of tabu iterations */
};


/******************************************************************************/
void read_instance(char* arquivo, int bin_types, vector<int> & binCap,
    vector<int> & binCost, vector<int> & weight, int items)
{
    FILE* fp;
    int i = 0;
    int j = 0;
    int tmp = 0;
    vector<int> d(2 * bin_types);

    fp = fopen(arquivo, "r");
    if (fp == NULL)
        exit(1);

    for (i = 0; i < 4; i++)
        fscanf(fp, "%d", &tmp);

    for (j = 0; j < bin_types * 2; j++)
    {
        fscanf(fp, "%d", &tmp);
        d[j] = tmp;
    }

    i = 0;
    for (j = 0; j < bin_types; j++)
    {
        binCap[j] = d[i];
        binCost[j] = d[i + 1];
        i += 2;
    }

    for (i = 0; i < items; i++)
    {
        fscanf(fp, "%d", &tmp);
        weight[i] = tmp;
    }

    fclose(fp);
}
/******************************************************************************/
void read_prob_sizes(char* arquivo, int* bin_types, int* items)
{
    FILE* fp;
    fp = fopen(arquivo, "r");
    if (fp == NULL)
        exit(1);

    fscanf(fp, "%d", items);
    fscanf(fp, "%d", bin_types);
    fclose(fp);
}
/******************************************************************************/
double calc_fitness(vector<int> & individuo, vector<int> & binCap, vector<int> & binCost,
    vector<int> & weight, int items, int bin_types, vector<int> & bin_item)
{
    double f = 0.0;
    int* Q; /* Peso acumulado */
    int* etiqueta_custo;
    int* etiqueta_pred;
    int i, j;
    int custo_acumulado = 0;
    int peso = 0;
    double penalidade = 0.0;
    double fi_bi = DBL_MAX; /* minima razao entre fi / bi (custo / capacidade) */
    double tmp = 0.0;
    int peso_excesso = 0;
    int peso_excesso_min = INT_MAX;

    int binNumber = 1;

    Q = (int*)malloc(sizeof(int) * (items + 1));
    etiqueta_custo = (int*)malloc(sizeof(int) * (items + 1));
    etiqueta_pred = (int*)malloc(sizeof(int) * (items + 1));

    for (i = 0; i < items + 1; i++)
    {
        etiqueta_custo[i] = 0;
        etiqueta_pred[i] = -1;
    }

    Q[0] = 0;
    for (i = 1; i < items + 1; i++)
        Q[i] = Q[i - 1] + weight[individuo[i - 1]];

    for (i = 0; i < items; i++)
    {
        for (j = i + 1; j < items + 1; j++)
        {
            int val = Q[j] - Q[i];
            int entrou = 0;
            custo_acumulado = etiqueta_custo[i];
            if (val <= binCap[0])
            {
                custo_acumulado += binCost[0];
                entrou = 1;
            }
            else if (val <= binCap[1])
            {
                custo_acumulado += binCost[1];
                entrou = 1;
            }
            else if (val <= binCap[2])
            {
                custo_acumulado += binCost[2];
                entrou = 1;
            }

            if (entrou)
            {
                if (etiqueta_pred[j] == -1 || custo_acumulado < etiqueta_custo[j])
                {
                    etiqueta_custo[j] = custo_acumulado /*+ etiqueta_custo[i]*/;
                    etiqueta_pred[j] = i;
                }
            }
            else
                break;
        }
    }

    f = etiqueta_custo[items];

    i = items;
    bin_item[i] = binNumber;
    do
    {
        for (j = i - 1; j >= etiqueta_pred[i]; j--)
            if (j < items)
                bin_item[j] = binNumber;

        i = etiqueta_pred[i];
        binNumber++;
    } while (i > 0);

#if DEBUG2
    for (i = 0; i < items; i++)
        printf("i = %d, individuo[%d] = %d, Peso[%d] = %d, bin_item[%d] = %d\n", i, i, individuo[i], individuo[i], weight[individuo[i]], i, bin_item[i]);
    printf("Custo = %.2f\n\n", f);
#endif

    free(Q);
    free(etiqueta_custo);
    free(etiqueta_pred);
    Q = NULL;
    etiqueta_custo = NULL;
    etiqueta_pred = NULL;
    return f;
}
/******************************************************************************/
void shuffle(int* array, size_t n, int seed)
{
    srand(seed);
    //srand(time(NULL)); /* descomente se preferir uma semente aleatoria a cada execucao */
    if (n > 1)
    {
        size_t i;
        for (i = 0; i < n - 1; i++)
        {
            size_t j = i + rand() / (RAND_MAX / (n - i) + 1);
            int t = array[j];
            array[j] = array[i];
            array[i] = t;
        }
    }
}
/******************************************************************************/
void sort(int* weight, int* individuo, int items)
{
    int i, j, temp;
    for (i = 0; i < items; i++)
    {
        for (j = i + 1; j < items; j++)
        {
            if (weight[individuo[i]] < weight[individuo[j]])
            {
                temp = individuo[i];
                individuo[i] = individuo[j];
                individuo[j] = temp;
            }
        }
    }
}
/******************************************************************************/
void generate_pop(vector< vector<double> > & pop, int pop_size, int lchrom)
{
    int i, j;
    time_t t;
    std::mt19937 generator((unsigned)time(&t));
    std::uniform_real_distribution<double> dis(0.0, 1.0);

    for (i = 0; i < pop_size; i++)
    {
        for (j = 0; j < lchrom; j++)
        {
            pop[i][j] = dis(generator);
        }
    }
}
/******************************************************************************/
void swap_double(int i, int j, vector<double> & v)
{
    double temp = v[i];
    v[i] = v[j];
    v[j] = temp;
}
/******************************************************************************/
void swap_int(int i, int j, vector<int> & v)
{
    int temp = v[i];
    v[i] = v[j];
    v[j] = temp;
}

/******************************************************************************/
void bubble_sort(vector<double> & d_vector, vector<int> & index, int lchrom)
{
    int out, in;
    for (out = lchrom - 1; out > 1; out--)
    {
        for (in = 0; in < out; in++)
        {
            if (d_vector[in] > d_vector[in + 1])
            {
                swap_double(in, in + 1, d_vector);
                swap_int(in, in + 1, index);
            }
        }
    }
}
/******************************************************************************/
void print_double(double* v, int size)
{
    int i;
    for (i = 0; i < size; i++)
    {
        printf("%.5f ", v[i]);
    }
    printf("\n");
}
/******************************************************************************/
void print_int(int* v, int size)
{
    int i;
    for (i = 0; i < size; i++)
    {
        printf("%d ", v[i]);
    }
    printf("\n");
}
/******************************************************************************/
void print_pop(vector< vector<double> >& pop, int pop_size, int lchrom)
{
    int i, j;
    for (i = 0; i < pop_size; i++)
    {
        printf("individuo %d = ", i + 1);
        for (j = 0; j < lchrom + 1; j++)
        {
            printf("%.3f ", pop[i][j]);
        }
        printf("\n");
    }
}
/******************************************************************************/
void swap_ind(int i, int j, vector< vector<double> > & pop, int lchrom)
{
    int k;
    vector<double> temp(lchrom + 1);

    for (k = 0; k < lchrom + 1; k++)
    {
        temp[k] = pop[i][k];
    }

    for (k = 0; k < lchrom + 1; k++)
    {
        pop[i][k] = pop[j][k];
    }

    for (k = 0; k < lchrom + 1; k++)
    {
        pop[j][k] = temp[k];
    }
}
/******************************************************************************/
void sort_pop(vector< vector<double> > & pop, int pop_size, int lchrom)
{
    int out, in;
    for (out = pop_size - 1; out > 1; out--)
    {
        for (in = 0; in < out; in++)
        {
            if (pop[in][lchrom] > pop[in + 1][lchrom])
            {
                swap_ind(in, in + 1, pop, lchrom);
            }
        }
    }
}
/******************************************************************************/
void compute_fitness_pop(vector< vector<double> > & pop, int pop_size, int lchrom, 
    vector<int> & binCap, vector<int> & binCost, vector<int> & weight,
    int bin_types, vector<int> & bin_item)
{
    int i, j;
    vector<double> tmp(lchrom + 1);
    vector<int> individuo(lchrom + 1);
    double myFitness = 0.0;
    for (i = 0; i < pop_size; i++)
    {
        for (j = 0; j < lchrom; j++)
        {
            tmp[j] = pop[i][j];
            individuo[j] = j;
        }
        bubble_sort(tmp, individuo, lchrom);
        myFitness = calc_fitness(individuo, binCap, binCost, weight, lchrom, bin_types, bin_item);
        pop[i][lchrom] = myFitness;
    }
}
/******************************************************************************/
double compute_fitness(vector<double> & ind, int lchrom, vector<int> & binCap, 
    vector<int> & binCost, vector<int> & weight, int bin_types, vector<int> & bin_item)
{
    int j;
    vector<int> individuo(lchrom + 1);
    double myFitness = 0.0;
    for (j = 0; j < lchrom; j++)
    {
        individuo[j] = j;
    }
    bubble_sort(ind, individuo, lchrom);
    myFitness = calc_fitness(individuo, binCap, binCost, weight, lchrom, bin_types, bin_item);
    return myFitness;
}
/******************************************************************************/
int get_rand_int(int lower, int upper)
{
    int num;
    num = (rand() % (upper - lower + 1)) + lower;
    return num;
}
/******************************************************************************/
void get_ind(vector< vector<double> > & pop, vector<double> & ind, int idx, int lchrom)
{
    int i;
    for (i = 0; i < lchrom + 1; i++)
    {
        ind[i] = pop[idx][i];
    }
}
/******************************************************************************/
void crossover(vector<double> & p1, vector<double> & p2, vector<double> & s, 
    double rhoe, int lchrom)
{
    int i;
    double r;
    time_t t;
    std::mt19937 generator((unsigned)time(&t));
    std::uniform_real_distribution<double> dis(0.0, 1.0);

    for (i = 0; i < lchrom + 1; i++)
    {
        r = dis(generator);
        if (r < rhoe)
        {
            s[i] = p1[i];
        }
        else {
            s[i] = p2[i];
        }
    }
}
/******************************************************************************/
void mating(vector< vector<double> > & pop, vector< vector<double> > & new_pop, 
    int pop_size, int lchrom, int ne, int nm, double rhoe)
{
    int i, j, k, l;
    time_t t;
    vector<double> ind1(lchrom + 1);
    vector<double> ind2(lchrom + 1);
    vector<double> s(lchrom + 1);

    srand((unsigned)time(0));
    std::mt19937 generator((unsigned)time(&t));
    std::uniform_real_distribution<double> dis(0.0, 1.0);

    /* Keep elite for the next generation */
    for (i = 0; i < pop_size; i++)
    {
        for (j = 0; j < lchrom + 1; j++)
        {
            new_pop[i][j] = pop[i][j];
        }
    }

    /* crossover between elite and non-elite */
    k = ne;
    l = pop_size - nm;
    for (k = ne; k < l; k++)
    {
        int idx_parent1 = get_rand_int(0, ne - 1);
        int idx_parent2 = get_rand_int(ne, l - 1);
        get_ind(pop, ind1, idx_parent1, lchrom);
        get_ind(pop, ind2, idx_parent2, lchrom);
        crossover(ind1, ind2, s, rhoe, lchrom);
        for (i = 0; i < lchrom + 1; i++)
        {
            new_pop[k][i] = s[i];
        }
    }

    /* Generate new mutants */
    for (k = l; k < pop_size; k++)
    {
        for (j = 0; j < lchrom; j++)
        {
            new_pop[i][j] = dis(generator);
        }
    }
}
/******************************************************************************/
void update_pop(vector< vector<double> >& pop, vector< vector<double> >& new_pop, 
    int pop_size, int lchrom)
{
    int i, j;
    for (i = 0; i < pop_size; i++)
    {
        for (j = 0; j < lchrom + 1; j++)
        {
            pop[i][j] = new_pop[i][j];
        }
    }
}
/******************************************************************************/
/**********************************************************************
 *                                                                    *
 *                         TABU SEARCH                                *
 *                                                                    *
 **********************************************************************/
void best_move(move_tabu* mov, int iter, double c_best, double c_curr,
    vector< vector<int> > & tabu_time, vector<int> & individuo, 
    int items, vector<int> & binCap,
    vector<int> & binCost, vector<int> & weight, int bin_types, 
    vector<int> & bin_item)
{
    int i, j, k;
    k = 0;
    mov->value = (double)INT_MAX;
    for (i = 0; i < items; i++)
    {
        for (j = 0; j < items; j++)
        {
            if (bin_item[i] != bin_item[j] && weight[individuo[i]] != weight[individuo[j]])
            {
                int tmp = individuo[i];
                individuo[i] = individuo[j];
                individuo[j] = tmp;
                c_curr = calc_fitness(individuo, binCap, binCost, weight, items, bin_types, bin_item);
                if (tabu_time[i][j] < iter || c_curr < c_best)
                {
                    if (c_curr < mov->value)
                    {
                        mov->value = c_curr;
                        mov->i = i;
                        mov->j = j;
#if DEBUG
                        printf("Entrou: mov->value = %.2f\n", mov->value);
#endif
                    }
                }
                tmp = individuo[j];
                individuo[j] = individuo[i];
                individuo[i] = tmp;
            }
        }
    }
}

void execute_move(move_tabu* mov, vector<int> & individuo)
{
    int tmp = individuo[mov->i];
    individuo[mov->i] = individuo[mov->j];
    individuo[mov->j] = tmp;
}

double tabu_search(vector<int> & individuo, vector<int> & binCap, vector<int> & binCost,
    vector<int> & weight, int items, int bin_types, double cost, vector<int> & bin_item,
    int tabu_size, int max_iter)
{
    double ts_cost = 0.0;
    int i, j;
    int iter;
    vector< vector<int> > tabu_time;
    vector<int> tmp_sol;
    vector<int> best_sol;
    double c_best, c_curr;
    move_tabu mov;
    
    tabu_time.resize(items);
    for (i = 0; i < items; i++)
        tabu_time[i].resize(items);
    
    tmp_sol.resize(items + 1);
    best_sol.resize(items + 1);

    for (i = 0; i < items; i++)
    {
        tmp_sol[i] = individuo[i];
        best_sol[i] = individuo[i];
        for (j = 0; j < items; j++)
            tabu_time[i][j] = 0;
    }
    tmp_sol[items] = individuo[items];
    best_sol[items] = individuo[items];

    iter = 0;
    c_curr = cost;
    c_best = c_curr;
    while (iter < max_iter)
    {
        iter++;
        best_move(&mov, iter, c_best, c_curr, tabu_time, tmp_sol, items, binCap, binCost, weight, bin_types, bin_item);
        execute_move(&mov, tmp_sol);
        tabu_time[mov.i][mov.j] = iter + tabu_size;
        c_curr = mov.value;
        if (c_curr < c_best)
        {
            c_best = c_curr;
            for (i = 0; i < items; i++)
                individuo[i] = tmp_sol[i];
            /*
            printf("Iter: %d) ", iter);
            printf("Cost = %.2f\n", c_best);
            printf("\n");
            */
        }


    }
    ts_cost = c_best;


    // ts_cost = calc_fitness(individuo, binCap, binCost, weight, items, bin_types, bin_item);
    // free_imatrix(tabu_time, 0, items, 0);
    // free(tmp_sol);
    // free(best_sol);
    return ts_cost;
}
/******************************************************************************/
void tabu_search_ind(vector< vector<double> >& pop, int pop_size, int lchrom, vector<int> & binCap,
    vector<int> & binCost, vector<int> & weight, int bin_types, 
    vector<int> & bin_item, int idx, int tabu_size, int max_iter)
{
    int j;
    vector<double> tmp(lchrom + 1);
    vector<double> tmp2(lchrom + 1);
    vector<int> individuo(lchrom + 1);
    double myFitness = 0.0;
    for (j = 0; j < lchrom; j++)
    {
        tmp[j] = pop[idx][j];
        tmp2[j] = pop[idx][j];
        individuo[j] = j;
    }
    bubble_sort(tmp, individuo, lchrom);
    myFitness = pop[idx][lchrom];

#if DEBUG
    printf("Custo antes: %.2f\n", myFitness);
    printf("Individuo antes: \n");
    for (int i = 0; i < lchrom; i++)
        printf("%d ", individuo[i]);
    printf("\n");

    printf("Individuo antes: \n");
    for (int i = 0; i < lchrom; i++)
        printf("%.3f ", tmp[i]);
    printf("\n");
#endif

    myFitness = tabu_search(individuo, binCap, binCost, weight, lchrom, bin_types, myFitness, bin_item, tabu_size, max_iter);

#if DEBUG
    printf("Custo depois: %.2f\n", myFitness);
    printf("Individuo depois: \n");
    for (int i = 0; i < lchrom; i++)
        printf("%d ", individuo[i]);
    printf("\n");

    printf("Individuo depois: \n");
    for (int i = 0; i < lchrom; i++)
    {
        tmp2[i] = tmp2[individuo[i]];
        printf("%.3f ", tmp2[i]);
    }
    printf("\n");
#endif
    pop[idx][lchrom] = myFitness;
    for (j = 0; j < lchrom; j++)
    {
        pop[idx][j] = tmp2[j];
    }
}
/******************************************************************************/
void rtrim(char* src)
{
    size_t i, len;
    volatile int isblank = 1;

    if (src == NULL) return;

    len = strlen(src);
    if (len == 0) return;
    for (i = len - 1; i > 0; i--)
    {
        isblank = isspace(src[i]);
        if (isblank)
            src[i] = 0;
        else
            break;
    }
    if (isspace(src[i]))
        src[i] = 0;
}
/******************************************************************************/
void ltrim(char* src)
{
    size_t i, len;

    if (src == NULL) return;

    i = 0;
    len = strlen(src);
    if (len == 0) return;
    while (src[i] && isspace(src[i]))
        i++;

    memmove(src, src + i, len - i + 1);
    return;
}
/******************************************************************************/
void trim(char* src)
{
    rtrim(src);
    ltrim(src);
}
/******************************************************************************/
int parse_line(struct config* config, char* buf)
{
    if (config == NULL || buf == NULL)
        return 0;

    char varname[100];
    char value[100];
    const char* sep = "=\n"; // get also rid of newlines
    char* token;

    token = strtok(buf, sep);

    strncpy(varname, token, sizeof varname);
    varname[sizeof(varname) - 1] = 0; // making sure that varname is C-String

    trim(varname);

    token = strtok(NULL, sep);

    if (token == NULL)
    {
        // line not in format var=val
        return 0;
    }

    strncpy(value, token, sizeof value);
    value[sizeof(varname) - 1] = 0;

    trim(value);

    if (strcmp(varname, "pop_size") == 0)
    {
        config->pop_size = atoi(value);
        return 1;
    }


    if (strcmp(varname, "max_gen") == 0)
    {
        config->max_gen = atoi(value);
        return 1;
    }

    if (strcmp(varname, "pe") == 0)
    {
        config->pe = atof(value);
        return 1;
    }

    if (strcmp(varname, "pm") == 0)
    {
        config->pm = atof(value);
        return 1;
    }

    if (strcmp(varname, "rhoe") == 0)
    {
        config->rhoe = atof(value);
        return 1;
    }

    if (strcmp(varname, "tabu_size") == 0)
    {
        config->tabu_size = atoi(value);
        return 1;
    }

    if (strcmp(varname, "max_iter") == 0)
    {
        config->max_iter = atoi(value);
        return 1;
    }


    // var=val not recognized
    return 0;
}
/******************************************************************************/
void remove_duplicates_in_elite(vector< vector<double> > & pop, int pop_size, 
    int lchrom, int ne, vector<int>& binCap, vector<int>& binCost, 
    vector<int>& weight, int bin_types, vector<int>& bin_item)
{

    int i, j;
    int has_duplicates = 0;
    map<int, int> hash;
    time_t t;
    std::mt19937 generator((unsigned)time(&t));
    std::uniform_real_distribution<double> dis(0.0, 1.0);

    for (i = 0; i < ne; i++)
    {
        int fitness = (int)pop[i][lchrom];
        if (hash.find(fitness) == hash.end())
        {
            // not found
            hash[fitness] = 1;
        }
        else {

            for (j = 0; j < lchrom; j++)
            {
                pop[i][j] = dis(generator);
            }
            vector<double> d(lchrom);
            for (int k = 0; k < lchrom; k++)
                d[k] = pop[i][k];
            double myFitness = compute_fitness(d, lchrom, binCap, binCost, weight, bin_types, bin_item);
            pop[i][lchrom] = myFitness;
            has_duplicates = 1;
        }
    }
    sort_pop(pop, pop_size, lchrom);
}
/******************************************************************************/
int main(int argc, char* argv[])
{
    clock_t start;
    time_t t;
    double tempo = 0.0;
    char arquivo[80];
    int bin_types = 0;
    int items = 0;
    vector<int> binCap;
    vector<int> binCost;
    vector<int> weight;
    vector<int> individuo;
    vector<int> bin_item(100);
    double myFitness = 0.0;
    int iseed; /* semente para geracao de numeros aleatorios */

    /* Parameters for BRKGA */
    vector< vector<double> > pop;
    vector< vector<double> > new_pop;
    int lchrom;        /* Size of the chromossome                                        */
    int gen;           /* Current generation                                             */
    int ne;            /* size of elite population                                       */
    int nm;            /* size of mutant population                                      */

    if (argc == 3)
    {
        sscanf(argv[1], "%s", arquivo);
        iseed = atoi(argv[2]);
    }
    else
    {
        printf("Wrong number of arguments: a.out <instance> <seed>\n");
        exit(1);
    }

    srand((unsigned)time(&t));



    struct config config;
    // initializing
    config.pop_size = 100;
    config.max_gen = 30;
    config.pe = 0.15;
    config.pm = 0.15;
    config.rhoe = 0.8;

    int linecnt = 0;
    char buffer[100];
    FILE* fp;
    fp = fopen("config.txt", "r");
    while (fgets(buffer, sizeof(buffer), fp) != NULL) {
        linecnt++;
        trim(buffer);
        if (buffer[0] == '#')
            continue;

        if (!parse_line(&config, buffer))
        {
            fprintf(stderr, "Error on line %d, ignoring.\n", linecnt);
            continue;
        }
    }

    ne = (int) config.pop_size * config.pe;
    nm = (int) config.pop_size * config.pm;

    /* Limit the size of elite population to 150 */
    if (ne > 150)
    {
        ne = 150;
    }

    read_prob_sizes(arquivo, &bin_types, &items);
    lchrom = items;
    binCap.resize(bin_types);
    binCost.resize(bin_types);
    weight.resize(items);
    individuo.resize(items + 1);

    read_instance(arquivo, bin_types, binCap, binCost, weight, items);

    pop.resize(config.pop_size);
    new_pop.resize(config.pop_size);
    for (int i = 0; i < config.pop_size; i++)
    {
        pop[i].resize(lchrom + 1);
        new_pop[i].resize(lchrom + 1);
    }

    start = clock();

    /* Generate intial population randomly */
    generate_pop(pop, config.pop_size, lchrom + 1);
    compute_fitness_pop(pop, config.pop_size, lchrom, binCap, binCost, weight, bin_types, bin_item);
    sort_pop(pop, config.pop_size, lchrom);
    // remove_duplicates_in_elite(pop, config.pop_size, lchrom, ne, binCap, binCost, weight, bin_types, bin_item);

    for (gen = 0; gen < config.max_gen; gen++)
    {
        mating(pop, new_pop, config.pop_size, lchrom, ne, nm, config.rhoe);
        update_pop(pop, new_pop, config.pop_size, lchrom);
        compute_fitness_pop(pop, config.pop_size, lchrom, binCap, binCost, weight, bin_types, bin_item);
        sort_pop(pop, config.pop_size, lchrom);
    }

    printf("\nPopucao final:\n");
    print_pop(pop, config.pop_size, lchrom);


    double best_cost = pop[0][lchrom];
    /* Run tabu search in the elite of the population */
    printf("Best cost before tabu search: %.2f\n", best_cost);
    for (int i = 0; i < ne; i++)
    {
        tabu_search_ind(pop, config.pop_size, lchrom, binCap, binCost,
            weight, bin_types, bin_item, i, config.tabu_size, config.max_iter);
        printf("Tabu search cost for elite %d: %.2f\n", i+1,  pop[i][lchrom]);
        if (pop[i][lchrom] < best_cost)
        {
            best_cost = pop[i][lchrom];
        }
    }

    printf("Best cost = %.2f\n", best_cost);
    tempo = (double)(clock() - start) / CLOCKS_PER_SEC;
    printf("CPU time = %.5f\n", tempo);

    return 0;
}