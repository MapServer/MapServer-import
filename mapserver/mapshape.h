#ifndef MAPSHAPE_H
#define MAPSHAPE_H

#include <stdio.h>
#include "mapprimitive.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifndef SWIG
#define MS_PATH_LENGTH 1024

// Shapefile types
#define SHP_POINT 1
#define SHP_ARC 3
#define SHP_POLYGON 5
#define SHP_MULTIPOINT 8

#define SHP_POINTZ 11
#define SHP_ARCZ  13
#define SHP_POLYGONZ 15
#define SHP_MULTIPOINTZ 18

#define SHP_POINTM 21
#define SHP_ARCM  23
#define SHP_POLYGONM 25
#define SHP_MULTIPOINTM 28
#endif

#define MS_SHAPEFILE_POINT 1
#define MS_SHAPEFILE_ARC 3
#define MS_SHAPEFILE_POLYGON 5
#define MS_SHAPEFILE_MULTIPOINT 8

#define MS_SHP_POINTZ 11
#define MS_SHP_ARCZ  13
#define MS_SHP_POLYGONZ 15
#define MS_SHP_MULTIPOINTZ 18

#define MS_SHP_POINTM 21
#define MS_SHP_ARCM  23
#define MS_SHP_POLYGONM 25
#define MS_SHP_MULTIPOINTM 28

#ifndef SWIG
typedef unsigned char uchar;

typedef	struct {
    FILE	*fpSHP;
    FILE	*fpSHX;

    int		nShapeType;				/* SHPT_* */
    int		nFileSize;				/* SHP file */

    int		nRecords;
    int		nMaxRecords;
    int		*panRecOffset;
    int		*panRecSize;

    double	adBoundsMin[4];
    double	adBoundsMax[4];

    int		bUpdated;

    int		nBufSize; // these used static vars in shape readers, moved to be thread-safe
    uchar   *pabyRec;
    int		nPartMax;
    int		*panParts;

} SHPInfo;
typedef SHPInfo * SHPHandle;
#endif

typedef	struct
{
#ifdef SWIG
%immutable;
#endif
    FILE	*fp;

    int		nRecords;

    int		nRecordLength;
    int		nHeaderLength;
    int		nFields;
    int		*panFieldOffset;
    int		*panFieldSize;
    int		*panFieldDecimals;
    char	*pachFieldType;

    char	*pszHeader;

    int		nCurrentRecord;
    int		bCurrentRecordModified;
    char	*pszCurrentRecord;
    
    int		bNoHeader;
    int		bUpdated;

    char 	*pszStringField;
    int		nStringFieldLen;    
#ifdef SWIG
%mutable;
#endif
} DBFInfo;
typedef DBFInfo * DBFHandle;

typedef enum {FTString, FTInteger, FTDouble, FTInvalid} DBFFieldType;

// Shapefile object, no write access via scripts                               
typedef struct {
#ifdef SWIG
%immutable;
#endif
  char source[MS_PATH_LENGTH]; // full path to this file data

#ifndef SWIG
  SHPHandle hSHP; // SHP/SHX file pointer
#endif

  int type; // shapefile type
  int numshapes; // number of shapes
  rectObj bounds; // shape extent

#ifndef SWIG
  DBFHandle hDBF; // DBF file pointer 
#endif

  int lastshape;

  char *status;
  rectObj statusbounds; // holds extent associated with the status vector

  int isopen;
#ifdef SWIG
%mutable;
#endif
} shapefileObj;

// layerInfo structure for tiled shapefiles
typedef struct { 
  shapefileObj *shpfile;
  shapefileObj *tileshpfile;
  int tilelayerindex;
} msTiledSHPLayerInfo;

#ifndef SWIG

// shapefileObj function prototypes 
MS_DLL_EXPORT int msSHPOpenFile(shapefileObj *shpfile, char *mode, char *filename);
MS_DLL_EXPORT int msSHPCreateFile(shapefileObj *shpfile, char *filename, int type);
MS_DLL_EXPORT void msSHPCloseFile(shapefileObj *shpfile);
MS_DLL_EXPORT int msSHPWhichShapes(shapefileObj *shpfile, rectObj rect, int debug);

// SHP/SHX function prototypes
MS_DLL_EXPORT SHPHandle msSHPOpen( const char * pszShapeFile, const char * pszAccess );
MS_DLL_EXPORT SHPHandle msSHPCreate( const char * pszShapeFile, int nShapeType );
MS_DLL_EXPORT void msSHPClose( SHPHandle hSHP );
MS_DLL_EXPORT void msSHPGetInfo( SHPHandle hSHP, int * pnEntities, int * pnShapeType );
MS_DLL_EXPORT int msSHPReadBounds( SHPHandle psSHP, int hEntity, rectObj *padBounds );
MS_DLL_EXPORT void msSHPReadShape( SHPHandle psSHP, int hEntity, shapeObj *shape );
MS_DLL_EXPORT int msSHPReadPoint(SHPHandle psSHP, int hEntity, pointObj *point );
MS_DLL_EXPORT int msSHPWriteShape( SHPHandle psSHP, shapeObj *shape );
MS_DLL_EXPORT int msSHPWritePoint(SHPHandle psSHP, pointObj *point );

// tiledShapefileObj function prototypes are in map.h

// XBase function prototypes
MS_DLL_EXPORT DBFHandle msDBFOpen( const char * pszDBFFile, const char * pszAccess );
MS_DLL_EXPORT void msDBFClose( DBFHandle hDBF );
MS_DLL_EXPORT DBFHandle msDBFCreate( const char * pszDBFFile );

MS_DLL_EXPORT int msDBFGetFieldCount( DBFHandle psDBF );
MS_DLL_EXPORT int msDBFGetRecordCount( DBFHandle psDBF );
MS_DLL_EXPORT int msDBFAddField( DBFHandle hDBF, const char * pszFieldName, DBFFieldType eType, int nWidth, int nDecimals );

MS_DLL_EXPORT DBFFieldType msDBFGetFieldInfo( DBFHandle psDBF, int iField, char * pszFieldName, int * pnWidth, int * pnDecimals );

MS_DLL_EXPORT int msDBFReadIntegerAttribute( DBFHandle hDBF, int iShape, int iField );
MS_DLL_EXPORT double msDBFReadDoubleAttribute( DBFHandle hDBF, int iShape, int iField );
MS_DLL_EXPORT const char *msDBFReadStringAttribute( DBFHandle hDBF, int iShape, int iField );

MS_DLL_EXPORT int msDBFWriteIntegerAttribute( DBFHandle hDBF, int iShape, int iField, int nFieldValue );
MS_DLL_EXPORT int msDBFWriteDoubleAttribute( DBFHandle hDBF, int iShape, int iField, double dFieldValue );
MS_DLL_EXPORT int msDBFWriteStringAttribute( DBFHandle hDBF, int iShape, int iField, const char * pszFieldValue );

MS_DLL_EXPORT char **msDBFGetItems(DBFHandle dbffile);
MS_DLL_EXPORT char **msDBFGetValues(DBFHandle dbffile, int record);
MS_DLL_EXPORT char **msDBFGetValueList(DBFHandle dbffile, int record, int *itemindexes, int numitems);
MS_DLL_EXPORT int *msDBFGetItemIndexes(DBFHandle dbffile, char **items, int numitems);
MS_DLL_EXPORT int msDBFGetItemIndex(DBFHandle dbffile, char *name);

#endif

#ifdef __cplusplus
}
#endif

#endif /* MAPSHAPE_H */
