/**********************************************************************
 * $Id$
 *
 * Name:     mapgraticule.c
 * Project:  MapServer
 * Language: C
 * Purpose:  Graticule Renderer
 * Author:   John Novak, Novacell Technologies (jnovak@novacell.com)
 *
 **********************************************************************
 * Copyright (c) 2003, John Novak, Novacell Technologies
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
 * DEALINGS IN THE SOFTWARE.
 **********************************************************************
 * $Log$
 * Revision 1.3  2003/02/15 20:26:22  novak
 * Initial graticule support
 *
 **********************************************************************/

#include "map.h"
#include "mapproject.h"

/**********************************************************************************************************************
 *
 */
typedef enum
{
	posBottom	= 1,
	posTop,
	posLeft,
	posRight
} msGraticulePosition;

typedef enum
{
	lpDefault	= 0,
	lpDDMMSS	= 1,
	lpDDMM,
} msLabelProcessingType;

void DefineAxis( int iTickCountTarget, double *Min, double *Max, double *Inc );
static void _AdjustLabelPosition( layerObj *pLayer, shapeObj *pShape, msGraticulePosition ePosition );
static void _FormatLabel( layerObj *pLayer, shapeObj *pShape, double dDataToFormat );

#define MAPGRATICULE_ARC_SUBDIVISION_DEFAULT	(256)
#define MAPGRATICULE_ARC_MINIMUM				 (16)
#define MAPGRATICULE_FORMAT_STRING_DEFAULT		"%5.2f"
#define MAPGRATICULE_FORMAT_STRING_DDMMSS		"%3d %02d %02d"
#define MAPGRATICULE_FORMAT_STRING_DDMM			"%3d %02d"

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerOpen(layerObj *layer) 
{
	graticuleObj 		*pInfo	= (graticuleObj *) layer->graticulelayerinfo;

	if( pInfo == NULL )
		return MS_FAILURE;

	pInfo->dincrementlatitude	=   15.0;
	pInfo->dincrementlongitude	=   15.0;
	pInfo->dwhichlatitude		=  -90.0;
	pInfo->dwhichlongitude		= -180.0;
	pInfo->bvertical			=    1;

	if( layer->class->label.size == -1 )
		pInfo->blabelaxes		= 0;
	else
		pInfo->blabelaxes		= 1;

	if( pInfo->pszlabelformat == NULL )
	{
		pInfo->pszlabelformat	= (char *) malloc( strlen( MAPGRATICULE_FORMAT_STRING_DEFAULT ) + 1 );
		pInfo->ilabeltype		= (int)    lpDefault;
		strcpy( pInfo->pszlabelformat, MAPGRATICULE_FORMAT_STRING_DEFAULT );
	}
	else if( strcmp( pInfo->pszlabelformat, "DDMMSS" )	== 0 )
	{
		pInfo->pszlabelformat	= (char *) malloc( strlen( MAPGRATICULE_FORMAT_STRING_DDMMSS ) + 1 );
		pInfo->ilabeltype		= (int)    lpDDMMSS;
		strcpy( pInfo->pszlabelformat, MAPGRATICULE_FORMAT_STRING_DDMMSS );
	}
	else if( strcmp( pInfo->pszlabelformat, "DDMM" )	== 0 )
	{
		pInfo->pszlabelformat	= (char *) malloc( strlen( MAPGRATICULE_FORMAT_STRING_DDMM ) + 1 );
		pInfo->ilabeltype		= (int)    lpDDMM;
		strcpy( pInfo->pszlabelformat, MAPGRATICULE_FORMAT_STRING_DDMM );
	}

	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerClose(layerObj *layer)
{
	graticuleObj 		*pInfo			= (graticuleObj *) layer->graticulelayerinfo;

	if( pInfo->pszlabelformat )
	{
		free( pInfo->pszlabelformat );
		pInfo->pszlabelformat			= NULL;
	}

	if( pInfo->pboundingpoints )
	{
		free( pInfo->pboundingpoints );
		pInfo->pboundingpoints			= NULL;
	}

	if( pInfo->pboundinglines )
	{
		free( pInfo->pboundinglines );
		pInfo->pboundinglines			= NULL;
	}

	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerWhichShapes(layerObj *layer, rectObj rect)
{
	graticuleObj 		*pInfo			= (graticuleObj *) layer->graticulelayerinfo;
	int					 iAxisTickCount	= 0;

	pInfo->dstartlatitude			= rect.miny;
	pInfo->dstartlongitude			= rect.minx;
	pInfo->dendlatitude				= rect.maxy;
	pInfo->dendlongitude			= rect.maxx;
	pInfo->bvertical				= 1;
	pInfo->extent					= rect;
	
	if( pInfo->dminarcs > 0 )
		iAxisTickCount				= (int) pInfo->dminarcs;
	else if( pInfo->dminarcs > 0 )
		iAxisTickCount				= (int) pInfo->dminarcs;
	
	DefineAxis( iAxisTickCount, &pInfo->dstartlongitude, &pInfo->dendlongitude,	&pInfo->dincrementlongitude );
	DefineAxis( iAxisTickCount, &pInfo->dstartlatitude,	&pInfo->dendlatitude,	&pInfo->dincrementlatitude  );

	pInfo->dwhichlatitude			= pInfo->dstartlatitude;
	pInfo->dwhichlongitude			= pInfo->dstartlongitude;

	if( pInfo->dminincrement > 0.0
	  && pInfo->dmaxincrement > 0.0
	  && pInfo->dminincrement == pInfo->dmaxincrement )
	{
		pInfo->dincrementlongitude	= pInfo->dminincrement;
		pInfo->dincrementlatitude	= pInfo->dminincrement;
	}
	else if( pInfo->dminincrement > 0.0 )
	{
		pInfo->dincrementlongitude	= pInfo->dminincrement;
		pInfo->dincrementlatitude	= pInfo->dminincrement;
	}
	else if( pInfo->dmaxincrement > 0.0 )
	{
		pInfo->dincrementlongitude	= pInfo->dmaxincrement;
		pInfo->dincrementlatitude	= pInfo->dmaxincrement;
	}
//
//  If using PROJ, project rect back into map system, and generate rect corner points in native system.
//  These lines will be used when generating labels to get correct placement at arc/rect edge intersections.
//
#ifdef USE_PROJ
	if( layer->map->projection.numargs > 0 
	  && layer->projection.numargs > 0 )
#endif
	{
		rectObj		 rectMapCoordinates	= layer->map->extent;
		pInfo->pboundinglines			= (lineObj *)  malloc( sizeof( lineObj )  * 4 );
		pInfo->pboundingpoints			= (pointObj *) malloc( sizeof( pointObj ) * 8 );
//
//  top
//
		pInfo->pboundinglines[0].numpoints		= 2;
		pInfo->pboundinglines[0].point			= &pInfo->pboundingpoints[0];
		pInfo->pboundinglines[0].point[0].x		= rectMapCoordinates.minx;
		pInfo->pboundinglines[0].point[0].y		= rectMapCoordinates.maxy;
		pInfo->pboundinglines[0].point[1].x		= rectMapCoordinates.maxx;
		pInfo->pboundinglines[0].point[1].y		= rectMapCoordinates.maxy;

#ifdef USE_PROJ
		msProjectLine( &layer->map->projection, &layer->projection, &pInfo->pboundinglines[0] );
#endif
//
//  bottom
//
		pInfo->pboundinglines[1].numpoints		= 2;
		pInfo->pboundinglines[1].point			= &pInfo->pboundingpoints[2];
		pInfo->pboundinglines[1].point[0].x		= rectMapCoordinates.minx;
		pInfo->pboundinglines[1].point[0].y		= rectMapCoordinates.miny;
		pInfo->pboundinglines[1].point[1].x		= rectMapCoordinates.maxx;
		pInfo->pboundinglines[1].point[1].y		= rectMapCoordinates.miny;

#ifdef USE_PROJ
		msProjectLine( &layer->map->projection, &layer->projection, &pInfo->pboundinglines[1] );
#endif
//
//  left
//
		pInfo->pboundinglines[2].numpoints		= 2;
		pInfo->pboundinglines[2].point			= &pInfo->pboundingpoints[4];
		pInfo->pboundinglines[2].point[0].x		= rectMapCoordinates.minx;
		pInfo->pboundinglines[2].point[0].y		= rectMapCoordinates.miny;
		pInfo->pboundinglines[2].point[1].x		= rectMapCoordinates.minx;
		pInfo->pboundinglines[2].point[1].y		= rectMapCoordinates.maxy;

#ifdef USE_PROJ
		msProjectLine( &layer->map->projection, &layer->projection, &pInfo->pboundinglines[2] );
#endif
//
//  right
//
		pInfo->pboundinglines[3].numpoints		= 2;
		pInfo->pboundinglines[3].point			= &pInfo->pboundingpoints[6];
		pInfo->pboundinglines[3].point[0].x		= rectMapCoordinates.maxx;
		pInfo->pboundinglines[3].point[0].y		= rectMapCoordinates.miny;
		pInfo->pboundinglines[3].point[1].x		= rectMapCoordinates.maxx;
		pInfo->pboundinglines[3].point[1].y		= rectMapCoordinates.maxy;

#ifdef USE_PROJ
		msProjectLine( &layer->map->projection, &layer->projection, &pInfo->pboundinglines[3] );
#endif
	}

	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerNextShape(layerObj *layer, shapeObj *shape)
{
	graticuleObj 		*pInfo		= (graticuleObj *) layer->graticulelayerinfo;

	if( pInfo->dminarcsubdivisions <= 0.0
	  || pInfo->dmaxarcsubdivisions <= 0.0 )
	{
		pInfo->dminarcsubdivisions	= 
		pInfo->dmaxarcsubdivisions	= MAPGRATICULE_ARC_SUBDIVISION_DEFAULT;
	}

	shape->numlines					= 1;
	shape->type						= MS_SHAPE_LINE;
	shape->line						= (lineObj *) malloc( sizeof( lineObj ) );

	shape->line->numpoints			= (int) pInfo->dmaxarcsubdivisions;	
//
//  Subdivide and draw current arc, rendering the arc labels first
//
	if( pInfo->bvertical )
	{
		int		iPointIndex;
		double	dArcDelta			= (pInfo->dendlatitude - pInfo->dstartlatitude) / (double) shape->line->numpoints;
		double  dArcPosition		= pInfo->dstartlatitude + dArcDelta;
		double	dStartY, dDeltaX;
		
		switch( pInfo->ilabelstate )
		{
			case 0:
				if( ! pInfo->blabelaxes )		//  Bottom
				{
					pInfo->ilabelstate++;
					return MS_SUCCESS;
				}

				dDeltaX							= (pInfo->dwhichlongitude - pInfo->pboundinglines[1].point[0].x) / (pInfo->pboundinglines[1].point[1].x - pInfo->pboundinglines[1].point[0].x );
				dStartY							= (pInfo->pboundinglines[1].point[1].y - pInfo->pboundinglines[1].point[0].y) * dDeltaX + pInfo->pboundinglines[1].point[0].y;
				shape->line->numpoints			= (int) 2;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * 2 );
				
				shape->line->point[0].x			= pInfo->dwhichlongitude;
				shape->line->point[0].y			= dStartY;
				shape->line->point[1].x			= pInfo->dwhichlongitude;
				shape->line->point[1].y			= dStartY + dArcDelta;

				_FormatLabel( layer, shape, shape->line->point[0].x );
				_AdjustLabelPosition( layer, shape, posBottom );

				pInfo->ilabelstate++;
				return MS_SUCCESS;

			case 1:
				if( ! pInfo->blabelaxes )		//  Top
				{
					pInfo->ilabelstate++;
					return MS_SUCCESS;
				}

				dDeltaX							= (pInfo->dwhichlongitude - pInfo->pboundinglines[0].point[0].x) / (pInfo->pboundinglines[0].point[1].x - pInfo->pboundinglines[0].point[0].x );
				dStartY							= (pInfo->pboundinglines[0].point[1].y - pInfo->pboundinglines[0].point[0].y) * dDeltaX + pInfo->pboundinglines[0].point[1].y;
				shape->line->numpoints			= (int) 2;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * 2 );

				shape->line->point[0].x			= pInfo->dwhichlongitude;
				shape->line->point[0].y			= dStartY - dArcDelta;
				shape->line->point[1].x			= pInfo->dwhichlongitude;
				shape->line->point[1].y			= dStartY;

				_FormatLabel( layer, shape, shape->line->point[0].x );
				_AdjustLabelPosition( layer, shape, posTop );

				pInfo->ilabelstate++;
				return MS_SUCCESS;

			case 2:
				shape->line->numpoints			= (int) shape->line->numpoints + 1;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * shape->line->numpoints );

				shape->line->point[0].x			= pInfo->dwhichlongitude;
				shape->line->point[0].y			= pInfo->dstartlatitude;

				for( iPointIndex = 1; iPointIndex < shape->line->numpoints; iPointIndex++ )
				{
					shape->line->point[iPointIndex].x	= pInfo->dwhichlongitude;
					shape->line->point[iPointIndex].y	= dArcPosition;
			
					dArcPosition					   += dArcDelta;
				}
				
				pInfo->ilabelstate				= 0;
				break;

			default:
				pInfo->ilabelstate				= 0;
				break;
		}
		
	}
	else
	{
		int		iPointIndex;
		double	dArcDelta			= (pInfo->dendlongitude - pInfo->dstartlongitude) / (double) shape->line->numpoints;
		double  dArcPosition		= pInfo->dstartlongitude + dArcDelta;
		double	dStartX, dDeltaY;

		switch( pInfo->ilabelstate )
		{
			case 0:
				if( ! pInfo->blabelaxes )			//  Left  side
				{
					pInfo->ilabelstate++;
					return MS_SUCCESS;
				}

				dDeltaY							= (pInfo->dwhichlatitude - pInfo->pboundinglines[2].point[0].y) / (pInfo->pboundinglines[2].point[1].y - pInfo->pboundinglines[2].point[0].y );
				dStartX							= (pInfo->pboundinglines[2].point[1].x - pInfo->pboundinglines[2].point[0].x) * dDeltaY + pInfo->pboundinglines[2].point[0].x;
				shape->line->numpoints			= (int) 2;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * 2 );
				
				shape->line->point[0].x			= dStartX;
				shape->line->point[0].y			= pInfo->dwhichlatitude;
				shape->line->point[1].x			= dStartX + dArcDelta;
				shape->line->point[1].y			= pInfo->dwhichlatitude;

				_FormatLabel( layer, shape, shape->line->point[0].y );
				_AdjustLabelPosition( layer, shape, posLeft );

				pInfo->ilabelstate++;
				return MS_SUCCESS;

			case 1:
				if( ! pInfo->blabelaxes )			//  Right side
				{
					pInfo->ilabelstate++;
					return MS_SUCCESS;
				}

				dDeltaY							= (pInfo->dwhichlatitude - pInfo->pboundinglines[3].point[0].y) / (pInfo->pboundinglines[3].point[1].y - pInfo->pboundinglines[3].point[0].y );
				dStartX							= (pInfo->pboundinglines[3].point[1].x - pInfo->pboundinglines[3].point[0].x) * dDeltaY + pInfo->pboundinglines[3].point[0].x;
				shape->line->numpoints			= (int) 2;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * 2 );

				shape->line->point[0].x			= dStartX - dArcDelta;
				shape->line->point[0].y			= pInfo->dwhichlatitude;
				shape->line->point[1].x			= dStartX;
				shape->line->point[1].y			= pInfo->dwhichlatitude;

				_FormatLabel( layer, shape, shape->line->point[0].y );
				_AdjustLabelPosition( layer, shape, posRight );

				pInfo->ilabelstate++;
				return MS_SUCCESS;

			case 2:
				shape->line->numpoints			= (int) shape->line->numpoints + 1;
				shape->line->point				= (pointObj *) malloc( sizeof( pointObj ) * shape->line->numpoints );

				shape->line->point[0].x			= pInfo->dstartlongitude;
				shape->line->point[0].y			= pInfo->dwhichlatitude;

				for( iPointIndex = 1; iPointIndex < shape->line->numpoints; iPointIndex++ )
				{
					shape->line->point[iPointIndex].x	= dArcPosition;
					shape->line->point[iPointIndex].y	= pInfo->dwhichlatitude;
			
					dArcPosition					   += dArcDelta;
				}
				
				pInfo->ilabelstate				= 0;
				break;

			default:
				pInfo->ilabelstate				= 0;
				break;
		}
	}
//
//  Increment and move to next arc
//
	pInfo->dwhichlatitude		   += pInfo->dincrementlatitude;

	if( pInfo->dwhichlatitude > pInfo->dendlatitude )
	{
		pInfo->dwhichlatitude		= pInfo->dstartlatitude;
		pInfo->dwhichlongitude	   += pInfo->dincrementlongitude;

		if( pInfo->dwhichlongitude > pInfo->dendlongitude
		  && pInfo->bvertical == 0 )
			return MS_DONE;
		else if( pInfo->dwhichlongitude > pInfo->dendlongitude )
		{
			pInfo->dwhichlatitude	= pInfo->dstartlatitude;
			pInfo->dwhichlongitude	= pInfo->dstartlongitude;
			pInfo->bvertical		= 0;
		}
	}

	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerGetItems(layerObj *layer)
{
	msGraticuleLayerInitItemInfo(layer);
	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerInitItemInfo(layerObj *layer)
{
	char **ppItemName	= (char **) malloc( sizeof( char * ) );

	*ppItemName			= (char *) malloc( 64 );
	strcpy( *ppItemName, "Graticule" );
	
	layer->numitems		= 1;
	layer->items		= ppItemName;
	
	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
void msGraticuleLayerFreeItemInfo(layerObj *layer)
{
	if( layer->items )
	{
		free( *((char **) layer->items) );
		free( ((char **) layer->items)  );
	}

	return;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerGetShape(layerObj *layer, shapeObj *shape, int tile, long record)
{
	return 0;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerGetExtent(layerObj *layer, rectObj *extent)
{
	graticuleObj 		*pInfo	= (graticuleObj  *) layer->graticulelayerinfo;

	if( pInfo )
	{
		*extent					= pInfo->extent;
		
		return MS_SUCCESS;
	}

	return MS_FAILURE;
}

/**********************************************************************************************************************
 *
 */
int msGraticuleLayerGetAutoStyle(mapObj *map, layerObj *layer, classObj *c, int tile, long record)
{
	return MS_SUCCESS;
}

/**********************************************************************************************************************
 *
 */
static void _FormatLabel( layerObj *pLayer, shapeObj *pShape, double dDataToFormat )
{
	graticuleObj 		*pInfo	= (graticuleObj  *) pLayer->graticulelayerinfo;
	char				cBuffer[32];
	int					iDegrees, iMinutes;
	
	switch( pInfo->ilabeltype )
	{
		case lpDDMMSS:
			iDegrees		= (int) dDataToFormat;
			dDataToFormat	= fabs( dDataToFormat - (double) iDegrees );
			
			iMinutes		= (int) (dDataToFormat * 60.0);
			dDataToFormat	= dDataToFormat - (((double) iMinutes) / 60.0);
			
			sprintf( cBuffer, pInfo->pszlabelformat, iDegrees, iMinutes, (int) (dDataToFormat * 3600.0) );
			break;
			
		case lpDDMM:
			iDegrees		= (int) dDataToFormat;
			dDataToFormat	= fabs( dDataToFormat - (double) iDegrees );
			
			sprintf( cBuffer, pInfo->pszlabelformat, iDegrees, (int) (dDataToFormat * 60.0) );
			break;

		case lpDefault:
		default:
			sprintf( cBuffer, pInfo->pszlabelformat, dDataToFormat );
	}
	
	pShape->text			= strdup( cBuffer );
}

/**********************************************************************************************************************
 *
 *  Move label position into display area by adjusting underlying shape line.
 */
static void _AdjustLabelPosition( layerObj *pLayer, shapeObj *pShape, msGraticulePosition ePosition )
{
	graticuleObj 		*pInfo	= (graticuleObj  *) pLayer->graticulelayerinfo;
	rectObj				 rectLabel;
	pointObj			 ptPoint;

	if( pInfo == NULL
	  || pShape == NULL )
		return;
	
	ptPoint			= pShape->line->point[0];

#ifdef USE_PROJ
    if( pLayer->project 
	  && msProjectionsDiffer( &pLayer->projection, &pLayer->map->projection ) )
		msProjectShape( &pLayer->projection, &pLayer->map->projection, pShape );
#endif

    if( pLayer->transform ) 
		msTransformShapeToPixel( pShape, pLayer->map->extent, pLayer->map->cellsize );

	msGetLabelSize( pShape->text, &pLayer->class[0].label, &rectLabel, &pLayer->map->fontset, 1.0 );

	switch( ePosition )
	{
		case posBottom:
			pShape->line->point[1].y = pLayer->map->height;
			pShape->line->point[0].y = pLayer->map->height - (fabs(rectLabel.maxy - rectLabel.miny) * 2 + 5);
			break;

		case posTop:
			pShape->line->point[1].y = 0;
			pShape->line->point[0].y = fabs(rectLabel.maxy - rectLabel.miny) * 2 + 5;
			break;

		case posLeft:
			pShape->line->point[1].x = 0;
			pShape->line->point[0].x = fabs(rectLabel.maxx - rectLabel.minx) * 2 + 5;
			break;
			
		case posRight:
			pShape->line->point[1].x = pLayer->map->width;
			pShape->line->point[0].x = pLayer->map->width - (fabs(rectLabel.maxx - rectLabel.minx) * 2 + 5);
			break;
	}

    if( pLayer->transform ) 
		msTransformPixelToShape( pShape, pLayer->map->extent, pLayer->map->cellsize );
	
#ifdef USE_PROJ
    if( pLayer->project 
	  && msProjectionsDiffer( &pLayer->map->projection, &pLayer->projection ) )
		msProjectShape( &pLayer->map->projection, &pLayer->projection, pShape );
#endif

	switch( ePosition )
	{
		case posBottom:
		case posTop:
			pShape->line->point[1].x = ptPoint.x;
			pShape->line->point[0].x = ptPoint.x;
			break;

		case posLeft:
		case posRight:
			pShape->line->point[1].y = ptPoint.y;
			pShape->line->point[0].y = ptPoint.y;
			break;
	}
}

/**********************************************************************************************************************
 **********************************************************************************************************************/
//  DefineAxes - Copyright (c) 2000, Michael P.D. Bramley.
//
//  Permission is granted to use this code without restriction as long as
//  this copyright notice appears in all source files.
//
//  Minor tweaks to incrment calculations - jnovak
//
void DefineAxis( int iTickCountTarget, double *Min, double *Max, double *Inc )
{
	// define local variables...

	double Test_inc,              // candidate increment value
		Test_min,              // minimum scale value
		Test_max,              // maximum scale value
		Range = *Max - *Min ;  // range of data

	int i = 0 ;                   // counter

	// don't create problems -- solve them

	if( Range < 0 ) 
	{
		*Inc = 0 ;
		return ;
	}

	// handle special case of repeated values

	else if( Range == 0) 
	{        
		*Min = ceil(*Max) - 1 ;
		*Max = *Min + 1 ;
		*Inc = 1 ;
		return ;
	}

	// compute candidate for increment

	Test_inc = pow( 10.0, ceil( log10( Range/10 ) ) ) ;

	// establish maximum scale value...

	Test_max = ( (long)(*Max / Test_inc)) * Test_inc ;

	if( Test_max < *Max )
		Test_max += Test_inc ;

	// establish minimum scale value...

	Test_min = Test_max ;

	do 
	{
		++i ;
		Test_min -= Test_inc ;
	}
	while( Test_min > *Min ) ;

	// subtracting small values can screw up the scale limits,
	// eg: if DefineAxis is called with (min,max)=(0.01, 0.1),
	// then the calculated scale is 1.0408E17 TO 0.05 BY 0.01.
	// the following if statment corrects for this...

	//if( fabs(Test_min) < 1E-10 )
	//   Test_min = 0 ;

	// adjust for too few tick marks

	if( iTickCountTarget <= 0 )
		iTickCountTarget	= MAPGRATICULE_ARC_MINIMUM;

	while( i < iTickCountTarget )
	{
		Test_inc /= 2 ;
		i		 *= 2 ;
	}

	if( i < 6 && 0 ) 
	{
		Test_inc /= 2 ;
		if( (Test_min + Test_inc) <= *Min )
			Test_min += Test_inc ;
		if( (Test_max - Test_inc) >= *Max )
			Test_max -= Test_inc ;
	}

	// pass back axis definition to caller

	*Min = Test_min ;
	*Max = Test_max ;
	*Inc = Test_inc ;
}

/**********************************************************************************************************************
 **********************************************************************************************************************/
