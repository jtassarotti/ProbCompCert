#ifndef PARSER_H_
#define PARSER_H_

int read_int(char *fp, int* i);
int read_real(char *fp,double* f);
void read_real_array(char *fp, double* arr, int N);
void read_int_array(char *fp, int* arr, int N);
char *get(char* s);
int parse(char* file);

#endif // PARSER_H_
