/******************************************************************************
 *
 * Project:  MapServer
 * Purpose:  projectionObj / PROJ.4 interface.
 * Author:   Steve Lime and the MapServer team.
 *
 ******************************************************************************
 * Copyright (c) 1996-2005 Regents of the University of Minnesota.
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
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 ******************************************************************************
 *
 * $Log$
 * Revision 1.47  2005/10/26 17:42:10  frank
 * Avoid warnings if USE_PROJ not defined.
 *
 * Revision 1.46  2005/10/20 19:37:19  frank
 * ensure reprojected polygons are closed
 *
 * Revision 1.45  2005/10/20 16:43:04  frank
 * msProjectShapeLine() implements RFC 5 line/polygon clipping at horizon
 *
 * Revision 1.44  2005/10/18 03:21:15  frank
 * fixed iteration in msProjectShape()
 *
 * Revision 1.43  2005/10/18 03:12:53  frank
 * delete unprojectable lines, NULL empty shapes (bug 411)
 *
 * Revision 1.42  2005/06/14 16:03:34  dan
 * Updated copyright date to 2005
 *
 * Revision 1.41  2005/04/21 15:09:28  julien
 * Bug1244: Replace USE_SHAPE_Z_M by USE_POINT_Z_M
 *
 * Revision 1.40  2005/04/14 15:17:14  julien
 * Bug 1244: Remove Z and M from point by default to gain performance.
 *
 * Revision 1.39  2005/03/08 18:08:01  frank
 * fixed msProjectPoint() to return MS_FAILURE in missing case: bug 1273
 *
 * Revision 1.38  2005/02/18 03:06:46  dan
 * Turned all C++ (//) comments into C comments (bug 1238)
 *
 * Revision 1.37  2004/11/16 21:56:18  dan
 * msGetEPSGProj() obsolete, replaced by msOWSGetEPSGProj() (bug 568)
 *
 * Revision 1.36  2004/10/29 20:27:06  dan
 * Rewritten msGetProjectionString() to avoid multiple reallocs
 *
 * Revision 1.35  2004/10/21 04:30:55  frank
 * Added standardized headers.  Added MS_CVSID().
 *
 */

#include "map.h"
#include "mapproject.h"
#include <assert.h>

MS_CVSID("$Id$")

#ifdef USE_PROJ
static int msTestNeedWrap( pointObj pt1, pointObj pt2, pointObj pt2_geo,
                           projectionObj *src_proj, 
                           projectionObj *dst_proj );
#endif

/************************************************************************/
/*                           msProjectPoint()                           */
/************************************************************************/
int msProjectPoint(projectionObj *in, projectionObj *out, pointObj *point)
{
#ifdef USE_PROJ
  projUV p;
  int	 error;

  if( in && in->gt.need_geotransform )
  {
      double x_out, y_out;

      x_out = in->gt.geotransform[0]
          + in->gt.geotransform[1] * point->x 
          + in->gt.geotransform[2] * point->y;
      y_out = in->gt.geotransform[3]
          + in->gt.geotransform[4] * point->x 
          + in->gt.geotransform[5] * point->y;

      point->x = x_out;
      point->y = y_out;
  }

/* -------------------------------------------------------------------- */
/*      If we have a fully defined input coordinate system and          */
/*      output coordinate system, then we will use pj_transform.        */
/* -------------------------------------------------------------------- */
  if( in && in->proj && out && out->proj )
  {
      double	z = 0.0;

      if( pj_is_latlong(in->proj) )
      {
          point->x *= DEG_TO_RAD;
          point->y *= DEG_TO_RAD;
      }

      error = pj_transform( in->proj, out->proj, 1, 0, 
                            &(point->x), &(point->y), &z );

      if( error || point->x == HUGE_VAL || point->y == HUGE_VAL )
          return MS_FAILURE;

      if( pj_is_latlong(out->proj) )
      {
          point->x *= RAD_TO_DEG;
          point->y *= RAD_TO_DEG;
      }
  }

/* -------------------------------------------------------------------- */
/*      Otherwise we fallback to using pj_fwd() or pj_inv() and         */
/*      assuming that the NULL projectionObj is supposed to be          */
/*      lat/long in the same datum as the other projectionObj.  This    */
/*      is essentially a backwards compatibility mode.                  */
/* -------------------------------------------------------------------- */
  else
  {
      /* nothing to do if the other coordinate system is also lat/long */
      if( in == NULL && out != NULL && pj_is_latlong(out->proj) )
          return MS_SUCCESS;
      if( out == NULL && in != NULL && pj_is_latlong(in->proj) )
          return MS_SUCCESS;

      p.u = point->x;
      p.v = point->y;

      if(in==NULL || in->proj==NULL) { /* input coordinates are lat/lon */
          p.u *= DEG_TO_RAD; /* convert to radians */
          p.v *= DEG_TO_RAD;  
          p = pj_fwd(p, out->proj);
      } else {
          if(out==NULL || out->proj==NULL) { /* output coordinates are lat/lon */
              p = pj_inv(p, in->proj);
              p.u *= RAD_TO_DEG; /* convert to decimal degrees */
              p.v *= RAD_TO_DEG;
          } else { /* need to go from one projection to another */
              p = pj_inv(p, in->proj);
              p = pj_fwd(p, out->proj);
          }
      }

      if( p.u == HUGE_VAL || p.v == HUGE_VAL )
          return MS_FAILURE;

      point->x = p.u;
      point->y = p.v;
  }

  if( out && out->gt.need_geotransform )
  {
      double x_out, y_out;

      x_out = out->gt.invgeotransform[0]
          + out->gt.invgeotransform[1] * point->x 
          + out->gt.invgeotransform[2] * point->y;
      y_out = out->gt.invgeotransform[3]
          + out->gt.invgeotransform[4] * point->x 
          + out->gt.invgeotransform[5] * point->y;

      point->x = x_out;
      point->y = y_out;
  }

  return(MS_SUCCESS);
#else
  msSetError(MS_PROJERR, "Projection support is not available.", "msProjectPoint()");
  return(MS_FAILURE);
#endif
}

/************************************************************************/
/*                         msProjectGrowRect()                          */
/************************************************************************/
#ifdef USE_PROJ
static void msProjectGrowRect(projectionObj *in, projectionObj *out, 
                              rectObj *prj_rect, int *rect_initialized, 
                              pointObj *prj_point, int *failure )

{
    if( msProjectPoint(in, out, prj_point) == MS_SUCCESS )
    {
        if( *rect_initialized )
        {
            prj_rect->miny = MS_MIN(prj_rect->miny, prj_point->y);
            prj_rect->maxy = MS_MAX(prj_rect->maxy, prj_point->y);
            prj_rect->minx = MS_MIN(prj_rect->minx, prj_point->x);
            prj_rect->maxx = MS_MAX(prj_rect->maxx, prj_point->x);
        }
        else
        {
            prj_rect->minx = prj_rect->maxx = prj_point->x;
            prj_rect->miny = prj_rect->maxy = prj_point->y;
            *rect_initialized = MS_TRUE;
        }
    }
    else
        (*failure)++;
}
#endif /* def USE_PROJ */

/************************************************************************/
/*                           msProjectRect()                            */
/************************************************************************/

#define NUMBER_OF_SAMPLE_POINTS 100

int msProjectRect(projectionObj *in, projectionObj *out, rectObj *rect) 
{
#ifdef USE_PROJ
  pointObj prj_point;
  rectObj prj_rect;
  int	  rect_initialized = MS_FALSE, failure=0;

  double dx, dy;
  double x, y;

  dx = (rect->maxx - rect->minx)/NUMBER_OF_SAMPLE_POINTS;
  dy = (rect->maxy - rect->miny)/NUMBER_OF_SAMPLE_POINTS;

  /* first ensure the top left corner is processed, even if the rect
     turns out to be degenerate. */

  prj_point.x = rect->minx;
  prj_point.y = rect->miny;
#ifdef USE_POINT_Z_M
  prj_point.z = 0.0;
  prj_point.m = 0.0;
#endif /* USE_POINT_Z_M */

  msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                    &failure);

  /* sample along top and bottom */
  if(dx > 0) {
    for(x=rect->minx; x<=rect->maxx; x+=dx) {
      prj_point.x = x;
      prj_point.y = rect->miny;
      msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                        &failure);
      
      prj_point.x = x;
      prj_point.y = rect->maxy;
      msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                        &failure);
    }
  }

  /* sample along left and right */
  if(dy > 0) {
    for(y=rect->miny; y<=rect->maxy; y+=dy) {
      prj_point.y = y;
      prj_point.x = rect->minx;    
      msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                        &failure);
      
      prj_point.x = rect->maxx;
      prj_point.y = y;
      msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                        &failure);
    }
  }

  /*
  ** If there have been any failures around the edges, then we had better
  ** try and fill in the interior to get a close bounds. 
  */
  if( failure > 0 )
  {
      failure = 0;
      for(x=rect->minx + dx; x<=rect->maxx; x+=dx) {
          for(y=rect->miny + dy; y<=rect->maxy; y+=dy) {
              prj_point.x = x;
              prj_point.y = y;
              msProjectGrowRect(in,out,&prj_rect,&rect_initialized,&prj_point,
                                &failure);
          }
      }

      if( !rect_initialized )
      {
          if( out == NULL || out->proj == NULL 
              || pj_is_latlong(in->proj) )
          {
              prj_rect.minx = -180;
              prj_rect.maxx = 180;
              prj_rect.miny = -90;
              prj_rect.maxy = 90;
          }
          else
          {
              prj_rect.minx = -22000000;
              prj_rect.maxx = 22000000;
              prj_rect.miny = -11000000;
              prj_rect.maxy = 11000000;
          }

          msDebug( "msProjectRect(): all points failed to reproject, trying to fall back to using world bounds ... hope this helps.\n" );
      }
      else
      {
          msDebug( "msProjectRect(): some points failed to reproject, doing internal sampling.\n" );
      }
  }

  rect->minx = prj_rect.minx;
  rect->miny = prj_rect.miny;
  rect->maxx = prj_rect.maxx;
  rect->maxy = prj_rect.maxy;

  if( !rect_initialized )
      return MS_FAILURE;
  else
      return(MS_SUCCESS);
#else
  msSetError(MS_PROJERR, "Projection support is not available.", "msProjectRect()");
  return(MS_FAILURE);
#endif
}

/************************************************************************/
/*                          msProjectSegment()                          */
/*                                                                      */
/*      Interpolate along a line segment for which one end              */
/*      reprojects and the other end does not.  Finds the horizon.      */
/************************************************************************/

static int msProjectSegment( projectionObj *in, projectionObj *out, 
                             pointObj *start, pointObj *end )

{
    pointObj testPoint, subStart, subEnd;

/* -------------------------------------------------------------------- */
/*      Without loss of generality we assume the first point            */
/*      reprojects, and the second doesn't.  If that is not the case    */
/*      then re-call with the points reversed.                          */
/* -------------------------------------------------------------------- */
    testPoint = *start;
    if( msProjectPoint( in, out, &testPoint ) == MS_FAILURE )
    {
        testPoint = *end;
        if( msProjectPoint( in, out, &testPoint ) == MS_FAILURE )
            return MS_FAILURE;
        else
            return msProjectSegment( in, out, end, start );
    }

/* -------------------------------------------------------------------- */
/*      We will apply a binary search till we are within out            */
/*      tolerance.                                                      */
/* -------------------------------------------------------------------- */
    subStart = *start;
    subEnd = *end;

#define TOLERANCE 0.01
    
    while( fabs(subStart.x - subEnd.x) 
           + fabs(subStart.y - subEnd.y) > TOLERANCE )
    {
        pointObj midPoint;

        midPoint.x = (subStart.x + subEnd.x) * 0.5;
        midPoint.y = (subStart.y + subEnd.y) * 0.5;
        
        testPoint = midPoint;
        
        if( msProjectPoint( in, out, &testPoint ) == MS_FAILURE )
            subEnd = midPoint;
        else
            subStart = midPoint;
    }

/* -------------------------------------------------------------------- */
/*      Now reproject the end points and return.                        */
/* -------------------------------------------------------------------- */
    *end = subStart;
    
    if( msProjectPoint( in, out, end ) == MS_FAILURE
        || msProjectPoint( in, out, start ) == MS_FAILURE )
        return MS_FAILURE;
    else
        return MS_SUCCESS;
}

/************************************************************************/
/*                         msProjectShapeLine()                         */
/*                                                                      */
/*      Reproject a single linestring, potentially splitting into       */
/*      more than one line string if there are over the horizon         */
/*      portions.                                                       */
/*                                                                      */
/*      For polygons, no splitting takes place, but over the horizon    */
/*      points are clipped, and one segment is run from the fall        */
/*      over the horizon point to the come back over the horizon point. */
/************************************************************************/

#ifdef USE_PROJ
static int 
msProjectShapeLine(projectionObj *in, projectionObj *out, 
                   shapeObj *shape, int line_index)

{
    int i;
    pointObj	lastPoint, thisPoint, wrkPoint, firstPoint;
    lineObj *line = shape->line + line_index;
    lineObj *line_out = line;
    int valid_flag = 0; /* 1=true, -1=false, 0=unknown */
    int numpoints_in = line->numpoints;
    int line_alloc = numpoints_in;
    int wrap_test;

    wrap_test = out->proj != NULL && pj_is_latlong(out->proj)
        && !pj_is_latlong(in->proj);

    line->numpoints = 0;

    if( numpoints_in > 0 )
        firstPoint = line->point[0];

/* -------------------------------------------------------------------- */
/*      Loop over all input points in linestring.                       */
/* -------------------------------------------------------------------- */
    for( i=0; i < numpoints_in; i++ )
    {
        int ms_err;
        wrkPoint = thisPoint = line->point[i];

        ms_err = msProjectPoint(in, out, &wrkPoint );

/* -------------------------------------------------------------------- */
/*      Apply wrap logic.                                               */
/* -------------------------------------------------------------------- */
        if( wrap_test && i > 0 && ms_err != MS_FAILURE )
        {
            double dist;
            pointObj pt1Geo;

            if( line_out->numpoints > 0 )
                pt1Geo = line_out->point[0];
            else
                pt1Geo = wrkPoint; /* this is a cop out */

            dist = wrkPoint.x - pt1Geo.x;
            if( fabs(dist) > 180.0 
                && msTestNeedWrap( thisPoint, firstPoint, 
                                   pt1Geo, in, out ) )
            {
                if( dist > 0.0 )
                    wrkPoint.x -= 360.0;
                else if( dist < 0.0 )
                    wrkPoint.x += 360.0;
            }
        }

/* -------------------------------------------------------------------- */
/*      Put result into output line with appropriate logic for          */
/*      failure breaking lines, etc.                                    */
/* -------------------------------------------------------------------- */
        if( ms_err == MS_FAILURE ) 
        {
            /* We have started out invalid */
            if( i == 0 )
            {
                valid_flag = -1;
            }
            
            /* valid data has ended, we need to work out the horizon */
            else if( valid_flag == 1 )
            {
                pointObj startPoint, endPoint;
                
                startPoint = lastPoint;
                endPoint = thisPoint;
                if( msProjectSegment( in, out, &startPoint, &endPoint ) 
                    == MS_SUCCESS )
                {
                    line_out->point[line_out->numpoints++] = endPoint;
                }
                valid_flag = -1;
            }

            /* Still invalid ... */
            else if( valid_flag == -1 )
            {
                /* do nothing */
            }
        }

        else
        {
            /* starting out valid. */
            if( i == 0 )
            {
                line_out->point[line_out->numpoints++] = wrkPoint;
                valid_flag = 1;
            }
            
            /* Still valid, nothing special */
            else if( valid_flag == 1 )
            {
                line_out->point[line_out->numpoints++] = wrkPoint;
            }
            
            /* we have come over the horizon, figure out where, start newline*/
            else
            {
                pointObj startPoint, endPoint;
                
                startPoint = lastPoint;
                endPoint = thisPoint;
                if( msProjectSegment( in, out, &endPoint, &startPoint ) 
                    == MS_SUCCESS )
                {
                    lineObj newLine;

                    /* force pre-allocation of lots of points room */
                    if( line_out->numpoints > 0 
                        && shape->type == MS_SHAPE_LINE )
                    {
                        newLine.numpoints = numpoints_in - i + 1;
                        newLine.point = line->point;
                        msAddLine( shape, &newLine );

                        /* new line is now lineout, but start without any points */
                        line_out = shape->line + shape->numlines-1;

                        line_out->numpoints = 0;

                        /* the shape->line array is realloc, refetch "line" */
                        line = shape->line + line_index;
                    }
                    else if( line_out == line
                             && line->numpoints >= i-2 )
                    {
                        newLine.numpoints = line->numpoints;
                        newLine.point = line->point;
                        msAddLine( shape, &newLine );

                        line = shape->line + line_index;

                        line_out = shape->line + shape->numlines-1;
                        line_out->numpoints = line->numpoints;
                        line->numpoints = 0;
                        
                        /*
                         * Now realloc this array large enough to hold all
                         * the points we could possibly need to add. 
                         */
                        line_alloc = line_alloc * 2;

                        line_out->point = (pointObj *) 
                            realloc(line_out->point, 
                                    sizeof(pointObj) * line_alloc);
                    }
                     
                    line_out->point[line_out->numpoints++] = startPoint;
                }
                line_out->point[line_out->numpoints++] = wrkPoint;
                valid_flag = 1;
            }
        }

        lastPoint = thisPoint;
    }

/* -------------------------------------------------------------------- */
/*      Make sure that polygons are closed, even if the trip over       */
/*      the horizon left them unclosed.                                 */
/* -------------------------------------------------------------------- */
    if( shape->type == MS_SHAPE_POLYGON 
        && line_out->numpoints > 2 
        && (line_out->point[0].x != line_out->point[line_out->numpoints-1].x
            || line_out->point[0].y != line_out->point[line_out->numpoints-1].y) )
    {
        msAddPointToLine( line_out, line_out->point + 0 );
    }

    return(MS_SUCCESS);
}
#endif

/************************************************************************/
/*                           msProjectShape()                           */
/************************************************************************/
int msProjectShape(projectionObj *in, projectionObj *out, shapeObj *shape)
{
#ifdef USE_PROJ
  int i;

  for( i = shape->numlines-1; i >= 0; i-- )
  {
      if( shape->type == MS_SHAPE_LINE || shape->type == MS_SHAPE_POLYGON )
      {
          if( msProjectShapeLine( in, out, shape, i ) == MS_FAILURE )
              msShapeDeleteLine( shape, i );
      }
      else if( msProjectLine(in, out, shape->line+i ) == MS_FAILURE )
      {
          msShapeDeleteLine( shape, i );
      }
  }

  if( shape->numlines == 0 )
  {
      msFreeShape( shape );
      return MS_FAILURE;
  }
  else
      return(MS_SUCCESS);
#else
  msSetError(MS_PROJERR, "Projection support is not available.", "msProjectShape()");
  return(MS_FAILURE);
#endif
}

/************************************************************************/
/*                           msProjectLine()                            */
/*                                                                      */
/*      This function is now normally only used for point data.         */
/*      msProjectShapeLine() is used for lines and polygons and has     */
/*      lots of logic to handle horizon crossing.                       */
/************************************************************************/

int msProjectLine(projectionObj *in, projectionObj *out, lineObj *line)
{
#ifdef USE_PROJ
  int i, be_careful = 1;

  if( be_careful )
      be_careful = out->proj != NULL && pj_is_latlong(out->proj)
          && !pj_is_latlong(in->proj);

  if( be_careful )
  {
      pointObj	startPoint, thisPoint; /* locations in projected space */

      startPoint = line->point[0];

      for(i=0; i<line->numpoints; i++)
      {
          double	dist;

          thisPoint = line->point[i];

          /* 
          ** Read comments before msTestNeedWrap() to better understand
          ** this dateline wrapping logic. 
          */
          msProjectPoint(in, out, &(line->point[i]));
          if( i > 0 )
          {
              dist = line->point[i].x - line->point[0].x;
              if( fabs(dist) > 180.0 )
              {
                  if( msTestNeedWrap( thisPoint, startPoint, 
                                      line->point[0], in, out ) )
                  {
                      if( dist > 0.0 )
                      {
                          line->point[i].x -= 360.0;
                      }
                      else if( dist < 0.0 )
                      {
                          line->point[i].x += 360.0;
                      }
                  }
              }

          }
      }
  }
  else
  {
      for(i=0; i<line->numpoints; i++)
      {
          if( msProjectPoint(in, out, &(line->point[i])) == MS_FAILURE )
              return MS_FAILURE;
      }
  }

  return(MS_SUCCESS);
#else
  msSetError(MS_PROJERR, "Projection support is not available.", "msProjectLine()");
  return(MS_FAILURE);
#endif
}

/************************************************************************/
/*                        msProjectionsDiffer()                         */
/************************************************************************/

/*
** Compare two projections, and return MS_TRUE if they differ. 
**
** For now this is implemented by exact comparison of the projection
** arguments, but eventually this should call a PROJ.4 function with
** more awareness of the issues.
**
** NOTE: MS_FALSE is returned if either of the projection objects
** has no arguments, since reprojection won't work anyways.
*/

int msProjectionsDiffer( projectionObj *proj1, projectionObj *proj2 )

{
    int		i;

    if( proj1->numargs == 0 || proj2->numargs == 0 )
        return MS_FALSE;

    if( proj1->numargs != proj2->numargs )
        return MS_TRUE;

    /* This test should be more rigerous. */
    if( proj1->gt.need_geotransform 
        || proj2->gt.need_geotransform )
        return MS_TRUE;

    for( i = 0; i < proj1->numargs; i++ )
    {
        if( strcmp(proj1->args[i],proj2->args[i]) != 0 )
            return MS_TRUE;
    }

    return MS_FALSE;
}

/************************************************************************/
/*                           msTestNeedWrap()                           */
/************************************************************************/
/*

Frank Warmerdam, Nov, 2001. 

See Also: 

http://mapserver.gis.umn.edu/bugs/show_bug.cgi?id=15

Proposal:

Modify msProjectLine() so that it "dateline wraps" objects when necessary
in order to preserve their shape when reprojecting to lat/long.  This
will be accomplished by:

1) As each vertex is reprojected, compare the X distance between that 
   vertex and the previous vertex.  If it is less than 180 then proceed to
   the next vertex without any special logic, otherwise:

2) Reproject the center point of the line segment from the last vertex to
   the current vertex into lat/long.  Does it's longitude lie between the
   longitudes of the start and end point.  If yes, return to step 1) for
   the next vertex ... everything is fine. 

3) We have determined that this line segment is suffering from 360 degree
   wrap to keep in the -180 to +180 range.  Now add or subtract 360 degrees
   as determined from the original sign of the distances.  

This is similar to the code there now (though disabled in CVS); however, 
it will ensure that big boxes will remain big, and not get dateline wrapped
because of the extra test in step 2).  However step 2 is invoked only very
rarely so this process takes little more than the normal process.  In fact, 
if we were sufficiently concerned about performance we could do a test on the
shape MBR in lat/long space, and if the width is less than 180 we know we never
need to even do test 1). 

What doesn't this resolve:

This ensures that individual lines are kept in the proper shape when 
reprojected to geographic space.  However, it does not:

 o Ensure that all rings of a polygon will get transformed to the same "side"
   of the world.  Depending on starting points of the different rings it is
   entirely possible for one ring to end up in the -180 area and another ring
   from the same polygon to end up in the +180 area.  We might possibly be
   able to achieve this though, by treating the multi-ring polygon as a whole
   and testing the first point of each additional ring against the last
   vertex of the previous ring (or any previous vertex for that matter).

 o It does not address the need to cut up lines and polygons into distinct
   chunks to preserve the correct semantics.  Really a polygon that 
   spaces the dateline in a -180 to 180 view should get split into two 
   polygons.  We haven't addressed that, though if it were to be addressed,
   it could be done as a followon and distinct step from what we are doing
   above.  In fact this sort of improvement (split polygons based on dateline
   or view window) should be done for all lat/long shapes regardless of 
   whether they are being reprojected from another projection. 

 o It does not address issues related to viewing rectangles that go outside
   the -180 to 180 longitude range.  For instance, it is entirely reasonable
   to want a 160 to 200 longitude view to see an area on the dateline clearly.
   Currently shapes in the -180 to -160 range which should be displayed in the
   180 to 200 portion of that view will not be because there is no recogition
   that they belong there. 


*/

#ifdef USE_PROJ
static int msTestNeedWrap( pointObj pt1, pointObj pt2, pointObj pt2_geo,
                           projectionObj *in, 
                           projectionObj *out )

{
    pointObj	middle;

    middle.x = (pt1.x + pt2.x) * 0.5;
    middle.y = (pt1.y + pt2.y) * 0.5;
    
    if( msProjectPoint( in, out, &pt1 ) == MS_FAILURE 
        || msProjectPoint( in, out, &pt2 ) == MS_FAILURE
        || msProjectPoint( in, out, &middle ) == MS_FAILURE )
        return 0;

    /* 
     * If the last point was moved, then we are considered due for a
     * move to.
     */
    if( fabs(pt2_geo.x-pt2.x) > 180.0 )
        return 1;

    /*
     * Otherwise, test to see if the middle point transforms
     * to be between the end points. If yes, no wrapping is needed.
     * Otherwise wrapping is needed.
     */
    if( (middle.x < pt1.x && middle.x < pt2_geo.x)
        || (middle.x > pt1.x && middle.x > pt2_geo.x) )
        return 1;
    else
        return 0;
}
#endif /* def USE_PROJ */

/************************************************************************/
/*                            msProjFinder()                            */
/************************************************************************/
#ifdef USE_PROJ
static char *ms_proj_lib = NULL;
static char *last_filename = NULL;

static const char *msProjFinder( const char *filename)

{
    if( last_filename != NULL )
        free( last_filename );

    if( filename == NULL )
        return NULL;

    if( ms_proj_lib == NULL )
        return filename;

    last_filename = (char *) malloc(strlen(filename)+strlen(ms_proj_lib)+2);
    sprintf( last_filename, "%s/%s", ms_proj_lib, filename );

    return last_filename;
}
#endif /* def USE_PROJ */

/************************************************************************/
/*                           msSetPROJ_LIB()                            */
/************************************************************************/
void msSetPROJ_LIB( const char *proj_lib )

{
#ifdef USE_PROJ
    static int finder_installed = 0;

    if( finder_installed == 0 )
    {
        finder_installed = 1;
        pj_set_finder( msProjFinder );
    }
    
    if( ms_proj_lib != NULL )
    {
        free( ms_proj_lib );
        ms_proj_lib = NULL;
    }

    if( last_filename != NULL )
    {
        free( last_filename );
        last_filename = NULL;
    }

    if( proj_lib != NULL )
        ms_proj_lib = strdup( proj_lib );
#endif
}

/************************************************************************/
/*                       msGetProjectionString()                        */
/*                                                                      */
/*      Return the projection string.                                   */
/************************************************************************/

char *msGetProjectionString(projectionObj *proj)
{
    char        *pszProjString = NULL;
    int         i = 0, nLen = 0;

    if (proj)
    {
/* -------------------------------------------------------------------- */
/*      Alloc buffer large enough to hold the whole projection defn     */
/* -------------------------------------------------------------------- */
        for (i=0; i<proj->numargs; i++)
        {
            if (proj->args[i])
                nLen += (strlen(proj->args[i]) + 2);
        }

        pszProjString = (char*)malloc(sizeof(char) * nLen+1);
        pszProjString[0] = '\0';

/* -------------------------------------------------------------------- */
/*      Plug each arg into the string with a '+' prefix                 */
/* -------------------------------------------------------------------- */
        for (i=0; i<proj->numargs; i++)
        {
            if (!proj->args[i] || strlen(proj->args[i]) == 0)
                continue;
            if (pszProjString[0] == '\0')
            {
                /* no space at beginning of line */
                if (proj->args[i][0] != '+')
                    strcat(pszProjString, "+");
            }
            else
            {
                if (proj->args[i][0] != '+')
                    strcat(pszProjString, " +");
                else
                    strcat(pszProjString, " ");
            }
            strcat(pszProjString, proj->args[i]);
        }
    }

    return pszProjString;
}

