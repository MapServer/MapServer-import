/**********************************************************************
 * $Id$
 *
 * Project:  MapServer
 * Purpose:  OGR Output (for WFS)
 * Author:   Frank Warmerdam (warmerdam@pobox.com)
 *
 **********************************************************************
 * Copyright (c) 2010, Frank Warmerdam <warmerdam@pobox.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in 
 * all copies of this Software or works derived from this Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
 * DEALINGS IN THE SOFTWARE.
 **********************************************************************/

#include <assert.h>
#include "mapserver.h"
#include "mapproject.h"
#include "mapthread.h"

#if defined(USE_OGR)
#  define __USE_LARGEFILE64 1
#  include "ogr_api.h"
#  include "cpl_conv.h"
#  include "cpl_vsi.h"
#  include "cpl_string.h"
#endif

MS_CVSID("$Id: mapogr.cpp 10544 2010-09-30 11:04:28Z tamas $")

#ifdef USE_OGR

/************************************************************************/
/*                       msInitOGROutputFormat()                        */
/************************************************************************/

int msInitDefaultOGROutputFormat( outputFormatObj *format )

{
    OGRSFDriverH   hDriver;

    msOGRInitialize();

/* -------------------------------------------------------------------- */
/*      check that this driver exists.  Note visiting drivers should    */
/*      be pretty threadsafe so don't bother acquiring the GDAL         */
/*      lock.                                                           */
/* -------------------------------------------------------------------- */
    hDriver = OGRGetDriverByName( format->driver+4 );
    if( hDriver == NULL )
    {
        msSetError( MS_MISCERR, "No OGR driver named `%s' available.", 
                    "msInitOGROutputFormat()", format->driver+4 );
        return MS_FAILURE;
    }

    if( !OGR_Dr_TestCapability( hDriver, ODrCCreateDataSource ) )
    {
        msSetError( MS_MISCERR, "OGR `%s' driver does not support output.", 
                    "msInitOGROutputFormat()", format->driver+4 );
        return MS_FAILURE;
    }

/* -------------------------------------------------------------------- */
/*      Initialize the object.                                          */
/* -------------------------------------------------------------------- */
    format->imagemode = MS_IMAGEMODE_FEATURE;
    format->renderer = MS_RENDER_WITH_OGR;

    /* perhaps we should eventually hardcode mimetypes and extensions
       for some formats? */

    return MS_SUCCESS;
}

/************************************************************************/
/*                       msOGRRecursiveFileList()                       */
/*                                                                      */
/*      Collect a list of all files under the named directory,          */
/*      including those in subdirectories.                              */
/************************************************************************/

char **msOGRRecursiveFileList( const char *path )
{
    char **file_list;
    char **result_list = NULL;
    int i;

    file_list = CPLReadDir( path );

    for( i = 0; file_list != NULL && file_list[i] != NULL; i++ )
    {
        char full_filename[MS_MAXPATHLEN];
        VSIStatBufL  sStatBuf;

        if( EQUAL(file_list[i],".") || EQUAL(file_list[i],"..") )
            continue;

        strncpy( full_filename, 
                 CPLFormFilename( path, file_list[i], NULL ),
                 sizeof(full_filename) );

        VSIStatL( full_filename, &sStatBuf );

        if( VSI_ISREG( sStatBuf.st_mode ) )
        {
            result_list = CSLAddString( result_list, full_filename );
        }
        else if( VSI_ISDIR( sStatBuf.st_mode ) )
        {
            char **subfiles = msOGRRecursiveFileList( full_filename );

            result_list = CSLMerge( result_list, subfiles );

            CSLDestroy( subfiles );
        }
    }

    CSLDestroy( file_list );

    return result_list;
}

/************************************************************************/
/*                           msOGRCleanupDS()                           */
/************************************************************************/
static void msOGRCleanupDS( const char *datasource_name )

{
    char **file_list;
    char path[MS_MAXPATHLEN];
    int i;
    
    strncpy( path, CPLGetPath( datasource_name ), sizeof(path) );
    file_list = CPLReadDir( path );

    for( i = 0; file_list != NULL && file_list[i] != NULL; i++ )
    {
        char full_filename[MS_MAXPATHLEN];
        VSIStatBufL  sStatBuf;

        if( EQUAL(file_list[i],".") || EQUAL(file_list[i],"..") )
            continue;

        strncpy( full_filename, 
                 CPLFormFilename( path, file_list[i], NULL ),
                 sizeof(full_filename) );

        VSIStatL( full_filename, &sStatBuf );

        if( VSI_ISREG( sStatBuf.st_mode ) )
        {
            VSIUnlink( full_filename );
        }
        else if( VSI_ISDIR( sStatBuf.st_mode ) )
        {
            char fake_ds_name[MS_MAXPATHLEN];
            strncpy( fake_ds_name, 
                     CPLFormFilename( full_filename, "abc.dat", NULL ),
                     sizeof(fake_ds_name) );
            msOGRCleanupDS( fake_ds_name );
        }
    }

    CSLDestroy( file_list );

    VSIRmdir( path );
}

/************************************************************************/
/*                          msOGRWriteShape()                           */
/************************************************************************/

static int msOGRWriteShape( layerObj *map_layer, OGRLayerH hOGRLayer, 
                            shapeObj *shape, gmlItemListObj *item_list )

{
    OGRGeometryH hGeom = NULL;
    OGRFeatureH hFeat;
    OGRErr eErr;
    int i, out_field;
    OGRwkbGeometryType eLayerGType, eFeatureGType = wkbUnknown;

/* -------------------------------------------------------------------- */
/*      Transform point geometry.                                       */
/* -------------------------------------------------------------------- */
    if( shape->type == MS_SHAPE_POINT )
    {
        if( shape->numlines != 1 || shape->line[0].numpoints != 1 )
        {
            msSetError(MS_MISCERR, 
                       "Failed on odd point geometry.", 
                       "msOGRWriteShape()");
            return MS_FAILURE;
        }

        hGeom = OGR_G_CreateGeometry( wkbPoint );
        OGR_G_SetPoint( hGeom, 0, 
                        shape->line[0].point[0].x,
                        shape->line[0].point[0].y,
                        0.0 );
    }

/* -------------------------------------------------------------------- */
/*      Transform line geometry.                                        */
/* -------------------------------------------------------------------- */
    else if(  shape->type == MS_SHAPE_LINE )
    {
        hGeom = OGR_G_CreateGeometry( wkbLineString );
        
        if( shape->numlines != 1 || shape->line[0].numpoints < 2 )
        {
            msSetError(MS_MISCERR, 
                       "Failed on odd line geometry.", 
                       "msOGRWriteShape()");
            return MS_FAILURE;
        }

        for( i = 0; i < shape->line[0].numpoints; i++ )
        {
            OGR_G_SetPoint( hGeom, i, 
                            shape->line[0].point[i].x,
                            shape->line[0].point[i].y,
                            0.0 );
        }
    }

/* -------------------------------------------------------------------- */
/*      Transform polygon geometry.                                     */
/* -------------------------------------------------------------------- */
    else if(  shape->type == MS_SHAPE_POLYGON )
    {
        int iRing;

        hGeom = OGR_G_CreateGeometry( wkbPolygon );
        
        if( shape->numlines < 1 )
        {
            msSetError(MS_MISCERR, 
                       "Failed on odd polygon geometry.", 
                       "msOGRWriteShape()");
            return MS_FAILURE;
        }

        for( iRing = 0; iRing < shape->numlines; iRing++ )
        {
            OGRGeometryH hRing = OGR_G_CreateGeometry( wkbLinearRing );

            for( i = 0; i < shape->line[iRing].numpoints; i++ )
            {
                OGR_G_SetPoint( hRing, i, 
                                shape->line[iRing].point[i].x,
                                shape->line[iRing].point[i].y,
                                0.0 );
            }

            OGR_G_AddGeometryDirectly( hGeom, hRing );
        }
    }

/* -------------------------------------------------------------------- */
/*      Consider trying to force the geometry to a new type if it       */
/*      doesn't match the layer.                                        */
/* -------------------------------------------------------------------- */
    eLayerGType = 
        wkbFlatten(OGR_FD_GetGeomType(OGR_L_GetLayerDefn(hOGRLayer)));

    if( hGeom != NULL )
        eFeatureGType = wkbFlatten(OGR_G_GetGeometryType( hGeom ));
    
#if defined(GDAL_VERSION_NUM) && (GDAL_VERSION_NUM >= 1800)

    if( hGeom != NULL 
        && eLayerGType == wkbPolygon
        && eFeatureGType != eLayerGType )
        hGeom = OGR_G_ForceToPolygon( hGeom );

    else if( hGeom != NULL 
             && eLayerGType == wkbMultiPolygon
             && eFeatureGType != eLayerGType )
        hGeom = OGR_G_ForceToMultiPolygon( hGeom );
        
    else if( hGeom != NULL 
             && eLayerGType == wkbMultiPoint
             && eFeatureGType != eLayerGType )
        hGeom = OGR_G_ForceToMultiPoint( hGeom );
        
    else if( hGeom != NULL 
             && eLayerGType == wkbMultiLineString
             && eFeatureGType != eLayerGType )
        hGeom = OGR_G_ForceToMultiLineString( hGeom );
        
#endif /* GDAL/OGR 1.8 or later */

/* -------------------------------------------------------------------- */
/*      Create the feature, and attach the geometry.                    */
/* -------------------------------------------------------------------- */
    hFeat = OGR_F_Create( OGR_L_GetLayerDefn( hOGRLayer ) );
    
    OGR_F_SetGeometryDirectly( hFeat, hGeom );

/* -------------------------------------------------------------------- */
/*      Set attributes.                                                 */
/* -------------------------------------------------------------------- */
    out_field = 0;
    for( i = 0; i < item_list->numitems; i++ )
    {
        gmlItemObj *item = item_list->items + i;

        if( !item->visible )
            continue;

        OGR_F_SetFieldString( hFeat, out_field++, shape->values[i] );
    }

/* -------------------------------------------------------------------- */
/*      Write out and cleanup.                                          */
/* -------------------------------------------------------------------- */
    eErr = OGR_L_CreateFeature( hOGRLayer, hFeat );

    OGR_F_Destroy( hFeat );

    if( eErr != OGRERR_NONE )
    {
        msSetError( MS_OGRERR, 
                    "Attempt to write feature failed (code=%d):\n%s",
                    "msOGRWriteShape()", 
                    (int) eErr,
                    CPLGetLastErrorMsg() );
    }

    if( eErr == OGRERR_NONE )
        return MS_SUCCESS;
    else
        return MS_FAILURE;
}

#endif /* def USE_OGR */

/************************************************************************/
/*                        msOGRWriteFromQuery()                         */
/************************************************************************/

int msOGRWriteFromQuery( mapObj *map, outputFormatObj *format, int sendheaders )

{
#ifndef USE_OGR
    msSetError(MS_OGRERR, "OGR support is not available.", 
               "msOGRWriteFromQuery()");
    return MS_FAILURE;
#else
/* -------------------------------------------------------------------- */
/*      Variable declarations.                                          */
/* -------------------------------------------------------------------- */
    OGRSFDriverH hDriver;
    OGRDataSourceH hDS;
    const char *storage;
    const char *fo_filename;
    const char *form;
    char datasource_name[MS_MAXPATHLEN];
    char base_dir[MS_MAXPATHLEN];
    char *request_dir = NULL;
    char **ds_options = NULL;
    char **layer_options = NULL;
    char **file_list = NULL;
    int iLayer, i;

/* -------------------------------------------------------------------- */
/*      Fetch the output format driver.                                 */
/* -------------------------------------------------------------------- */
    msOGRInitialize();

    hDriver = OGRGetDriverByName( format->driver+4 );
    if( hDriver == NULL )
    {
        msSetError( MS_MISCERR, "No OGR driver named `%s' available.", 
                    "msOGRWriteFromQuery()", format->driver+4 );
        return MS_FAILURE;
    }

/* -------------------------------------------------------------------- */
/*      Capture datasource and layer creation options.                  */
/* -------------------------------------------------------------------- */
    for( i=0; i < format->numformatoptions; i++ )
    {
        if( strncasecmp(format->formatoptions[i],"LCO:",4) == 0 )
            layer_options = CSLAddString( layer_options, 
                                          format->formatoptions[i] + 4 );
        if( strncasecmp(format->formatoptions[i],"DSCO:",5) == 0 )
            ds_options = CSLAddString( ds_options, 
                                       format->formatoptions[i] + 4 );
    }
    
/* ==================================================================== */
/*      Determine the output datasource name to use.                    */
/* ==================================================================== */
    storage = msGetOutputFormatOption( format, "STORAGE", "filesystem" );

/* -------------------------------------------------------------------- */
/*      Where are we putting stuff?                                     */
/* -------------------------------------------------------------------- */
    if( EQUAL(storage,"filesystem") )
    {
        if( map->web.imagepath )
            strcpy( base_dir, map->web.imagepath ); /* should this be treated as relative to mappath? */
        else
            strcpy( base_dir, "/tmp/" );
    }
    else if( EQUAL(storage,"memory") )
    {
        strcpy( base_dir, "/vsimem/ogr_out/" );
    }
    else if( EQUAL(storage,"stream") )
    {
        /* handled later */
    }
    else
    {
        msSetError( MS_MISCERR, 
                    "STORAGE=%s value not supported.",
                    "msOGRWriteFromQuery()", 
                    storage );
        return MS_FAILURE;
    }

/* -------------------------------------------------------------------- */
/*      Create a subdirectory to handle this request.                   */
/* -------------------------------------------------------------------- */
    if( !EQUAL(storage,"stream") )
    {
        request_dir = msTmpFile( NULL, base_dir, "" );

        if( request_dir[strlen(request_dir)-1] == '.' )
            request_dir[strlen(request_dir)-1] = '\0';

        if( VSIMkdir( request_dir, 0777 ) != 0 )
        {
            msSetError( MS_MISCERR, 
                        "Attempt to create directory '%s' failed.",
                        "msOGRWriteFromQuery()", 
                        request_dir );
            return MS_FAILURE;
        }
    }
    else
        /* handled later */;

/* -------------------------------------------------------------------- */
/*      Setup the full datasource name.                                 */
/* -------------------------------------------------------------------- */
    fo_filename = msGetOutputFormatOption( format, "FILENAME", "result.dat" );

    if( !EQUAL(storage,"stream") )
        msBuildPath( datasource_name, request_dir, fo_filename );
    else
        strcpy( datasource_name, "/vsistdout/" );
    
    msFree( request_dir );

/* -------------------------------------------------------------------- */
/*      Emit content type headers for stream output now.                */
/* -------------------------------------------------------------------- */
    if( EQUAL(storage,"stream") )
    {
        if( sendheaders && format->mimetype )
            msIO_fprintf( stdout, 
                          "Content-Type: %s%c%c",
                          format->mimetype, 10, 10 );
        else
            msIO_fprintf( stdout, "%c", 10 );
    }

/* ==================================================================== */
/*      Create the datasource.                                          */
/* ==================================================================== */
    hDS = OGR_Dr_CreateDataSource( hDriver,  datasource_name, ds_options );
    
    if( hDS == NULL )
    {
        msOGRCleanupDS( datasource_name );
        msSetError( MS_MISCERR, 
                    "OGR CreateDataSource failed for '%s' with driver '%s'.",
                    "msOGRWriteFromQuery()", 
                    datasource_name, 
                    format->driver+4 );
        return MS_FAILURE;
    }

/* ==================================================================== */
/*      Process each layer with a resultset.                            */
/* ==================================================================== */
    for( iLayer = 0; iLayer < map->numlayers; iLayer++ )
    {
        int status;
        layerObj *layer = GET_LAYER(map, iLayer);
        shapeObj resultshape;
        OGRLayerH hOGRLayer;
        OGRwkbGeometryType eGeomType;
        OGRSpatialReferenceH srs = NULL;
        gmlItemListObj *item_list = NULL;
        const char *value;

        if( !layer->resultcache || layer->resultcache->numresults == 0 )
            continue;

/* -------------------------------------------------------------------- */
/*      Establish the geometry type to use for the created layer.       */
/*      First we consult the wfs_geomtype field and fallback to         */
/*      deriving something from the type of the mapserver layer.        */
/* -------------------------------------------------------------------- */
        value = msOWSLookupMetadata(&(layer->metadata), "FO", "geomtype");
        if( value == NULL )
        {
            if( layer->type == MS_LAYER_POINT )
                value = "Point";
            else if( layer->type == MS_LAYER_LINE )
                value = "LineString";
            else if( layer->type == MS_LAYER_POLYGON )
                value = "Polygon";
            else
                value = "Geometry";
        }

        if( strcasecmp(value,"Point") == 0 )
            eGeomType = wkbPoint;
        else if( strcasecmp(value,"LineString") == 0 )
            eGeomType = wkbLineString;
        else if( strcasecmp(value,"Polygon") == 0 )
            eGeomType = wkbPolygon;
        else if( strcasecmp(value,"MultiPoint") == 0 )
            eGeomType = wkbMultiPoint;
        else if( strcasecmp(value,"MultiLineString") == 0 )
            eGeomType = wkbMultiLineString;
        else if( strcasecmp(value,"MultiPolygon") == 0 )
            eGeomType = wkbMultiPolygon;
        else if( strcasecmp(value,"GeometryCollection") == 0 )
            eGeomType = wkbMultiPolygon;
        else if( strcasecmp(value,"Unknown") == 0 
                 || strcasecmp(value,"Geometry") == 0 )
            eGeomType = wkbUnknown;
        else if( strcasecmp(value,"None") == 0 )
            eGeomType = wkbNone;
        else
            eGeomType = wkbUnknown;
        
/* -------------------------------------------------------------------- */
/*      Create the corresponding OGR Layer.                             */
/* -------------------------------------------------------------------- */
        hOGRLayer = OGR_DS_CreateLayer( hDS, layer->name, srs, eGeomType, 
                                        layer_options );
        if( hOGRLayer == NULL )
        {
            msOGRCleanupDS( datasource_name );
            msSetError( MS_MISCERR, 
                        "OGR CreateDataSource failed for '%s' with driver '%s'.",
                        "msOGRWriteFromQuery()", 
                        datasource_name, 
                        format->driver+4 );
            return MS_FAILURE;
        }

/* -------------------------------------------------------------------- */
/*      Create appropriate attributes on this layer.                    */
/* -------------------------------------------------------------------- */
        item_list = msGMLGetItems( layer, "G" );
        assert( item_list->numitems == layer->numitems );
        
        for( i = 0; i < layer->numitems; i++ )
        {
            OGRFieldDefnH hFldDefn;
            OGRErr eErr;
            const char *name;
            gmlItemObj *item = item_list->items + i;
            OGRFieldType eType;
            
            if( !item->visible )
                continue;

            if( item->alias )
                name = item->alias;
            else
                name = item->name;
            
            if( item->type == NULL )
                eType = OFTString;
            else if( EQUAL(item->type,"Integer") )
                eType = OFTInteger;
            else if( EQUAL(item->type,"Real") )
                eType = OFTReal;
            else if( EQUAL(item->type,"Character") )
                eType = OFTString;
            else if( EQUAL(item->type,"Date") )
                eType = OFTDateTime;
            else if( EQUAL(item->type,"Boolean") )
                eType = OFTInteger;
            else 
                eType = OFTString;
            
            hFldDefn = OGR_Fld_Create( name, eType );
            
            if( item->width != 0 )
                OGR_Fld_SetWidth( hFldDefn, item->width );
            if( item->precision != 0 )
                OGR_Fld_SetPrecision( hFldDefn, item->precision );

            eErr = OGR_L_CreateField( hOGRLayer, hFldDefn, FALSE );
            OGR_Fld_Destroy( hFldDefn );

            if( eErr != OGRERR_NONE )
            {
                msSetError( MS_OGRERR, 
                            "Failed to create field '%s' in output feature schema:\n%s", 
                            "msOGRWriteFromQuery()", 
                            layer->items[i], 
                            CPLGetLastErrorMsg() );
                
                msOGRCleanupDS( datasource_name );
                return MS_FAILURE;
            }
        }

/* -------------------------------------------------------------------- */
/*      Setup joins if needed.  This is likely untested.                */
/* -------------------------------------------------------------------- */
        if(layer->numjoins > 0) {
            int j;
            for(j=0; j<layer->numjoins; j++) {
                status = msJoinConnect(layer, &(layer->joins[j]));
                if(status != MS_SUCCESS) {
                    msOGRCleanupDS( datasource_name );
                    return status;
                }
            }
        }

        msInitShape( &resultshape );

/* -------------------------------------------------------------------- */
/*      Loop over all the shapes in the resultcache.                    */
/* -------------------------------------------------------------------- */
        for(i=0; i < layer->resultcache->numresults; i++) {

            /*
            ** Read the shape.
            */
            status = msLayerResultsGetShape(
                layer, &resultshape,  layer->resultcache->results[i].tileindex,
                layer->resultcache->results[i].shapeindex );
            if(status != MS_SUCCESS) {
                msOGRCleanupDS( datasource_name );
                return status;
            } 

            /* 
            ** Perform classification, and some annotation related magic.
            */
            resultshape.classindex = 
                msShapeGetClass(layer, &resultshape, 
                                map->scaledenom, NULL, -1);

            if( resultshape.classindex >= 0 
                && (layer->class[resultshape.classindex]->text.string 
                    || layer->labelitem) 
                && layer->class[resultshape.classindex]->label.size != -1 )
            {
                resultshape.text = msShapeGetAnnotation(layer, &resultshape);
            }

            /*
            ** prepare any necessary JOINs here (one-to-one only)
            */
            if( layer->numjoins > 0) {
                int j;

                for(j=0; j < layer->numjoins; j++) {
                    if(layer->joins[j].type == MS_JOIN_ONE_TO_ONE) {
                        msJoinPrepare(&(layer->joins[j]), &resultshape);
                        msJoinNext(&(layer->joins[j])); /* fetch the first row */
                    }
                }
            }

            /*
            ** Write out the feature to OGR.
            */
            status = msOGRWriteShape( layer, hOGRLayer, &resultshape,
                                      item_list );
            if(status != MS_SUCCESS) {
                msOGRCleanupDS( datasource_name );
                return status;
            } 
        }

        msGMLFreeItems(item_list);
        msFreeShape(&resultshape); /* init too */
    }
    
/* -------------------------------------------------------------------- */
/*      Close the datasource.                                           */
/* -------------------------------------------------------------------- */
    OGR_DS_Destroy( hDS );
    
/* -------------------------------------------------------------------- */
/*      Get list of resulting files.                                    */
/* -------------------------------------------------------------------- */
#if !defined(CPL_ZIP_API_OFFERED)
    form = msGetOutputFormatOption( format, "FORM", "multipart" );
#else
    form = msGetOutputFormatOption( format, "FORM", "zip" );
#endif

    if( EQUAL(form,"simple") )
    {
        file_list = CSLAddString( NULL, datasource_name );
    }
    else
    {
        char datasource_path[MS_MAXPATHLEN];

        strcpy( datasource_path, CPLGetPath( datasource_name ) );
        file_list = msOGRRecursiveFileList( datasource_path );
    }

/* -------------------------------------------------------------------- */
/*      If our "storage" is stream then the output has already been     */
/*      sent back to the client and we don't need to copy it now.       */
/* -------------------------------------------------------------------- */
    if( EQUAL(storage,"stream") )
    {
        /* already done */
    }

/* -------------------------------------------------------------------- */
/*      Handle case of simple file written to stdout.                   */
/* -------------------------------------------------------------------- */
    else if( EQUAL(form,"simple") )
    {
        char buffer[1024];
        int  bytes_read;
        FILE *fp;

        if( sendheaders )
            msIO_fprintf( stdout, 
                          "Content-Disposition: attachment; filename=%s\n",
                          CPLGetFilename( file_list[0] ) );

        if( sendheaders && format->mimetype )
            msIO_fprintf( stdout, 
                          "Content-Type: %s%c%c",
                          format->mimetype, 10, 10 );
        else
            msIO_fprintf( stdout, "%c", 10 );

        fp = VSIFOpenL( file_list[0], "r" );
        if( fp == NULL )
        {
            msSetError( MS_MISCERR, 
                        "Failed to open result file '%s'.",
                        "msOGRWriteFromQuery()",
                        file_list[0] );
            msOGRCleanupDS( datasource_name );
            return MS_FAILURE;
        }

        while( (bytes_read = VSIFReadL( buffer, 1, sizeof(buffer), fp )) > 0 )
            msIO_fwrite( buffer, 1, bytes_read, stdout );
        VSIFCloseL( fp );
    }

/* -------------------------------------------------------------------- */
/*      Handle the case of a multi-part result.                         */
/* -------------------------------------------------------------------- */
    else if( EQUAL(form,"multipart") )
    {
        static const char *boundary = "xxOGRBoundaryxx";
        msIO_fprintf( stdout, 
                      "Content-Type: multipart/mixed; boundary=%s%c%c"
                      "--%s\n",
                      boundary, 10, 10, boundary );

        for( i = 0; file_list != NULL && file_list[i] != NULL; i++ )
        {
            FILE *fp;
            int bytes_read;
            char buffer[1024];

            if( sendheaders )
                msIO_fprintf( stdout, 
                              "Content-Disposition: attachment; filename=%s\n"
                              "Content-Type: application/binary\n"
                              "Content-Transfer-Encoding: binary%c%c",
                              CPLGetFilename( file_list[i] ),
                              10, 10 );

            
            fp = VSIFOpenL( file_list[i], "r" );
            if( fp == NULL )
            {
                msSetError( MS_MISCERR, 
                            "Failed to open result file '%s'.",
                            "msOGRWriteFromQuery()",
                            file_list[0] );
                msOGRCleanupDS( datasource_name );
                return MS_FAILURE;
            }
            
            while( (bytes_read = VSIFReadL( buffer, 1, sizeof(buffer), fp )) > 0 )
                msIO_fwrite( buffer, 1, bytes_read, stdout );
            VSIFCloseL( fp );

            if (file_list[i+1] == NULL)
                msIO_fprintf( stdout, "\n--%s--\n", boundary );
            else
                msIO_fprintf( stdout, "\n--%s\n", boundary );
        }
    }

/* -------------------------------------------------------------------- */
/*      Handle the case of a zip file result.                           */
/* -------------------------------------------------------------------- */
    else if( EQUAL(form,"zip") )
    {
#if !defined(CPL_ZIP_API_OFFERED)
        msSetError( MS_MISCERR, "FORM=zip selected, bug CPL ZIP support unavailable, perhaps you need to upgrade to GDAL/OGR 1.8?", 
                    "msOGRWriteFromQuery()");
        msOGRCleanupDS( datasource_name );
        return MS_FAILURE;
#else
        FILE *fp;
        char *zip_filename = msTmpFile( NULL, "/vsimem/ogrzip/", "zip" );
        void *hZip;
        int bytes_read;
        char buffer[1024];
        
        hZip = CPLCreateZip( zip_filename, NULL );
        
        for( i = 0; file_list != NULL && file_list[i] != NULL; i++ )
        {

            CPLCreateFileInZip( hZip, CPLGetFilename(file_list[i]), NULL );

            fp = VSIFOpenL( file_list[i], "r" );
            if( fp == NULL )
            {
                msSetError( MS_MISCERR, 
                            "Failed to open result file '%s'.",
                            "msOGRWriteFromQuery()",
                            file_list[0] );
                msOGRCleanupDS( datasource_name );
                return MS_FAILURE;
            }
            
            while( (bytes_read = VSIFReadL( buffer, 1, sizeof(buffer), fp )) > 0 )
            {
                CPLWriteFileInZip( hZip, buffer, bytes_read );
            }
            VSIFCloseL( fp );
            
            CPLCloseFileInZip( hZip );
        }
        CPLCloseZip( hZip );

        if( sendheaders )
            msIO_fprintf( stdout, 
                          "Content-Disposition: attachment; filename=%s\n"
                          "Content-Type: application/zip%c%c",
                          fo_filename, 10, 10 );

        fp = VSIFOpenL( zip_filename, "r" );
        if( fp == NULL )
        {
            msSetError( MS_MISCERR, 
                        "Failed to open zip file '%s'.",
                        "msOGRWriteFromQuery()",
                        file_list[0] );
            msOGRCleanupDS( datasource_name );
            return MS_FAILURE;
        }
            
        while( (bytes_read = VSIFReadL( buffer, 1, sizeof(buffer), fp )) > 0 )
            msIO_fwrite( buffer, 1, bytes_read, stdout );
        VSIFCloseL( fp );

        msFree( zip_filename );
#endif /* defined(CPL_ZIP_API_OFFERED) */
    }

/* -------------------------------------------------------------------- */
/*      Handle illegal form value.                                      */
/* -------------------------------------------------------------------- */
    else
    {
        msSetError( MS_MISCERR, "Unsupported FORM=%s value.", 
                    "msOGRWriteFromQuery()", form );
        msOGRCleanupDS( datasource_name );
        return MS_FAILURE;
    }

    msOGRCleanupDS( datasource_name );

    CSLDestroy( file_list );

    return MS_SUCCESS;
#endif /* def USE_OGR */
}

/************************************************************************/
/*                     msPopulateRenderVTableOGR()                      */
/************************************************************************/

int msPopulateRendererVTableOGR( rendererVTableObj *renderer )
{
#ifdef USE_OGR
    /* we aren't really a normal renderer so we leave everything default */
    return MS_SUCCESS;
#else
    msSetError(MS_OGRERR, "OGR Driver requested but is not built in", 
               "msPopulateRendererVTableOGR()");
    return MS_FAILURE;
#endif
}
