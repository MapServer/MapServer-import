#ifndef MAPPRIMITIVE_H
#define MAPPRIMITIVE_H

/* feature primitives */
typedef struct {
  double minx, miny, maxx, maxy;
} rectObj;

typedef struct {
  double x;
  double y;
} vectorObj;

typedef struct {
  double x;
  double y;
  double m;  
} pointObj;

typedef struct {
#ifdef SWIG
%immutable;
#endif
  int numpoints;
  pointObj *point;
#ifdef SWIG
%mutable;
#endif
} lineObj;

typedef struct {
#ifdef SWIG
%immutable;
#endif
  int numlines;
  int numvalues;
  lineObj *line;
  char **values;
#ifdef SWIG
%mutable;
#endif

  rectObj bounds;
  int type; // MS_SHAPE_TYPE
  long index;
  int tileindex;
  int classindex;
  char *text;
} shapeObj;

typedef lineObj multipointObj;

/* attribute primatives */
typedef struct {
  char *name;
  long type;
  int index;
  int size;
  short numdecimals;
} itemObj;

#endif /* MAPPRIMITIVE_H */
