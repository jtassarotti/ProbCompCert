#include "jsmn.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

struct nlist { 
    struct nlist *next; 
    char *name; 
    char *defn; 
};

static struct nlist *dict = NULL;

char *get(char *s) {
  struct nlist *np;
  for (np = dict; np != NULL; np = np->next) {
    if (strcmp(s, np->name) == 0) {
      return np->defn;
    }
  }
  printf("Missing field: %s\n", s);
  exit(EXIT_FAILURE);
}

void put(char *s) {

  struct nlist *np;
  np = (struct nlist *) malloc(sizeof(*np));
  np->name = s;
  np->next = dict;
  dict = np;
  
}

void print_dict() {

  printf("Printing complete dictionnary\n");
  static struct nlist *np;
  for (np = dict; np != NULL; np = np->next) {
    printf("%s \n", np->name);
  }
  printf("Done\n");
  
}

static int parse_primitive(const char *js, jsmntok_t *t, size_t count, int indent) {
  int i, j, k;
  jsmntok_t *key;
  if (count == 0) {
    return 0;
  }
  if (t->type == JSMN_PRIMITIVE) {
    int length = t->end - t->start;
    char *s = malloc(sizeof(char) * length);
    for (int i = 0; i < length; ++i) {
      s[i] = *(js + t->start + i);
    }
    printf("%.*s", t->end - t->start, js + t->start);
    return 1;
  } else {
    printf("Formating error: nested arrays\n");
    exit(EXIT_FAILURE);
  }
  return 0;
}

static int parse_defn(const char *js, jsmntok_t *t, size_t count, int indent) {
  int i, j, k;
  jsmntok_t *key;
  if (count == 0) {
    return 0;
  }
  if (t->type == JSMN_PRIMITIVE) {
    int length = t->end - t->start;
    char *s = malloc(sizeof(char) * length);
    for (int i = 0; i < length; ++i) {
      s[i] = *(js + t->start + i);
    }
    dict->defn = s;
    printf("%.*s", t->end - t->start, js + t->start);
    return 1;
  } else if (t->type == JSMN_STRING) {
    printf("Formating error: no strings in Stan data and parameters declarations\n");
    exit(EXIT_FAILURE);
  } else if (t->type == JSMN_OBJECT) {
    printf("Formating error: no objects in Stan data and parameters declarations\n");
    exit(EXIT_FAILURE);
  } else if (t->type == JSMN_ARRAY) {
    int length = t->end - t->start;
    char *s = malloc(sizeof(char) * length - 2);
    int idx = 0;
    j = 0;
    printf("\n");
    for (i = 0; i < t->size; i++) {
      for (k = 0; k < indent - 1; k++) {
        printf("  ");
      }
      int tok_length = t[1 + j].end - t[1 + j].start;
      for (int offset = 0; offset < tok_length; ++offset) {
	s[idx] = *(js + t[1 + j].start + offset);
	idx += 1;
      }
      printf("   - ");
      j += parse_primitive(js, t + 1 + j, count - j, indent + 1);
      printf("\n");
      s[idx] = ' ';
      idx += 1;
    }
    dict->defn = s;    
    return j + 1;
  }
  return 0;
}

static int parse_name(const char *js, jsmntok_t *t, size_t count, int indent) {
  int i, j, k;
  jsmntok_t *key;
  if (count == 0) {
    return 0;
  }
  if (t->type != JSMN_STRING) {
    printf("Formatting error, expected a string\n");
    exit(EXIT_FAILURE);
  } else if (t->type == JSMN_STRING) {
    int length = t->end - t->start;
    char *s = malloc(sizeof(char) * length);
    for (int i = 0; i < length; ++i) {
      s[i] = *(js + t->start + i);
    }
    printf("'%s'", s);
    put(s);
    return 1;
  } 
  return 0;
}

static int entry(const char *js, jsmntok_t *t, size_t count, int indent) {
  int i, j, k;
  jsmntok_t *key;
  if (count == 0) {
    return 0;
  }
  if (t->type != JSMN_OBJECT) {
    printf("Formatting error");
    exit(EXIT_FAILURE);
  } else if (t->type == JSMN_OBJECT) {
    printf("\n");
    j = 0;
    for (i = 0; i < t->size; i++) {
      for (k = 0; k < indent; k++) {
        printf("  ");
      }
      key = t + 1 + j;
      j += parse_name(js, key, count - j, indent + 1);
      if (key->size > 0) {
        printf(": ");
        j += parse_defn(js, t + 1 + j, count - j, indent + 1);
      }
      printf("\n");
    }
    return j + 1;
  }

  return 0;
}

static inline void *realloc_it(void *ptrmem, size_t size) {
  void *p = realloc(ptrmem, size);
  if (!p) {
    free(ptrmem);
    fprintf(stderr, "realloc(): errno=%d\n", errno);
  }
  return p;
}

int parse(char* file) {

  FILE *fp;
  fp = fopen(file, "r");
  
  int r;
  int eof_expected = 0;
  char *js = NULL;
  size_t jslen = 0;
  char buf[BUFSIZ];

  jsmn_parser p;
  jsmntok_t *tok;
  size_t tokcount = 2;

  /* Prepare parser */
  jsmn_init(&p);

  /* Allocate some tokens as a start */
  tok = malloc(sizeof(*tok) * tokcount);
  if (tok == NULL) {
    fprintf(stderr, "malloc(): errno=%d\n", errno);
    return 3;
  }

  for (;;) {
    /* Read another chunk */
    r = fread(buf, 1, sizeof(buf), fp);
    if (r < 0) {
      fprintf(stderr, "fread(): %d, errno=%d\n", r, errno);
      return 1;
    }
    if (r == 0) {
      if (eof_expected != 0) {
        return 0;
      } else {
        fprintf(stderr, "fread(): unexpected EOF\n");
        return 2;
      }
    }

    js = realloc_it(js, jslen + r + 1);
    if (js == NULL) {
      return 3;
    }
    strncpy(js + jslen, buf, r);
    jslen = jslen + r;

  again:
    r = jsmn_parse(&p, js, jslen, tok, tokcount);
    if (r < 0) {
      if (r == JSMN_ERROR_NOMEM) {
        tokcount = tokcount * 2;
        tok = realloc_it(tok, sizeof(*tok) * tokcount);
        if (tok == NULL) {
	  printf("test\n");
          return 3;
        }
        goto again;
      }
    } else {
      entry(js, tok, p.toknext, 0);
      eof_expected = 1;
    }
  }
  
  return EXIT_SUCCESS;
}

int read_int(char *defn, int* i) {

  int pos;
  sscanf(defn, "%i%n", i, &pos);
  return pos;

}

void read_int_array(char *defn, int* arr, int N) {

  int offset = 0;
  
  for (int i = 0; i < N; i++) {

    offset += read_int(defn + offset,arr + i);
    
  }
  
}

int read_real(char *defn,double* f) {

  int pos;
  sscanf(defn, "%lf%n", f, &pos);
  return pos;

}

void read_real_array(char *defn, double* arr, int N) {

  int offset = 0;
  
  for (int i = 0; i < N; i++) {

    offset += read_real(defn + offset,arr + i);
    
  }
  
}
