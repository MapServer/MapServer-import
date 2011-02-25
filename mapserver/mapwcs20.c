/******************************************************************************
 * $Id: mapwcs20.c
 *
 * Project:  MapServer
 * Purpose:  OpenGIS Web Coverage Server (WCS) 2.0 implementation.
 * Author:   Stephan Meissl <stephan.meissl@eox.at>
 *           Fabian Schindler <fabian.schindler@eox.at>
 *
 ******************************************************************************
 * Copyright (c) 2010 EOX IT Services GmbH, Austria
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
 ****************************************************************************/

#if defined(USE_WCS_SVR)

#include <assert.h>
#include "mapserver.h"
#include "maperror.h"
#include "mapthread.h"
#include "mapwcs.h"
#include <float.h>
#include "gdal.h"
#include "cpl_port.h"
#include "maptime.h"
#include "mapprimitive.h"
#include "cpl_string.h"
#include <proj_api.h>
#include <string.h>

#if defined(USE_LIBXML2)

    #include <libxml/tree.h>
    #include "maplibxml2.h"
    #include <libxml/parser.h>

#endif /* defined(USE_LIBXML2) */

/************************************************************************/
/*                   msStringParseInteger()                             */
/*                                                                      */
/*      Tries to parse a string as a integer value. If not possible     */
/*      the value MS_WCS20_UNBOUNDED is stored as value.                */
/*      If no characters could be parsed, MS_FAILURE is returned. If at */
/*      least some characters could be parsed, MS_DONE is returned and  */
/*      only if all characters could be parsed, MS_SUCCESS is returned. */
/************************************************************************/

static int msStringParseInteger(const char *string, int *dest)
{
    char *parse_check;
    *dest = (int)strtol(string, &parse_check, 0);
    if(parse_check == string)
    {
        return MS_FAILURE;
    }
    else if(parse_check - strlen(string) != string)
    {
        return MS_DONE;
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msStringParseDouble()                              */
/*                                                                      */
/*      Tries to parse a string as a double value. If not possible      */
/*      the value 0 is stored as value.                                 */
/*      If no characters could be parsed, MS_FAILURE is returned. If at */
/*      least some characters could be parsed, MS_DONE is returned and  */
/*      only if all characters could be parsed, MS_SUCCESS is returned. */
/************************************************************************/

static int msStringParseDouble(const char *string, double *dest)
{
    char *parse_check = NULL;
    *dest = strtod(string, &parse_check);
    if(parse_check == string)
    {
        return MS_FAILURE;
    }
    else if(parse_check - strlen(string) != string)
    {
        return MS_DONE;
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseTimeOrScalar20()                         */
/*                                                                      */
/*      Parses a string, either as a time or a scalar value and         */
/*      writes the output into the timeScalarUnion.                     */
/************************************************************************/

static int msWCSParseTimeOrScalar20(timeScalarUnion *u, const char *string)
{
    struct tm time;
    msStringTrim((char *) string);

    if (!string || strlen(string) == 0 || !u)
    {
        msSetError(MS_WCSERR, "Invalid string", "msWCSParseTimeOrScalar20()");
        return MS_WCS20_ERROR_VALUE;
    }
    /* if the string is equal to "*" it means the value
     *  of the interval is unbounded                    */
    if (EQUAL(string, "*"))
    {
        u->scalar = MS_WCS20_UNBOUNDED;
        u->unbounded = 1;
        return MS_WCS20_UNDEFINED_VALUE;
    }

    /* if returned a valid value, use it */
    if (msStringParseDouble(string, &(u->scalar)) == MS_SUCCESS)
    {
        return MS_WCS20_SCALAR_VALUE;
    }
    /* otherwise it might be a time value */
    msTimeInit(&time);
    if (msParseTime(string, &time) == MS_TRUE)
    {
        u->time = mktime(&time);
        return MS_WCS20_TIME_VALUE;
    }
    /* the value could neither be parsed as a double nor as a time value */
    else
    {
        msSetError(MS_WCSERR,
                "String %s could not be parsed to a time or scalar value",
                "msWCSParseTimeOrScalar20()");
        return MS_WCS20_ERROR_VALUE;
    }
}

/************************************************************************/
/*                   msStringIsNCName()                                 */
/*                                                                      */
/*      Evaluates if a string is a valid NCName.                        */
/************************************************************************/

static int msStringIsNCName(char *string)
{
    return msEvalRegex("^[a-zA-z_][a-zA-Z0-9_.-]*$" , string);
}

/************************************************************************/
/*                   msWCSCreateSubsetObj20()                           */
/*                                                                      */
/*      Creates a new wcs20SubsetObj and initializes it to standard     */
/*      values.                                                         */
/************************************************************************/

static wcs20SubsetObjPtr msWCSCreateSubsetObj20()
{
    wcs20SubsetObjPtr subset = (wcs20SubsetObjPtr) malloc(sizeof(wcs20SubsetObj));
    MS_CHECK_ALLOC(subset, sizeof(wcs20SubsetObj), NULL);

    subset->axis = NULL;
    subset->crs = NULL;
    subset->min.scalar = subset->max.scalar = MS_WCS20_UNBOUNDED;
    subset->min.unbounded = subset->max.unbounded = 0;
    subset->operation = MS_WCS20_SLICE;

    return subset;
}

/************************************************************************/
/*                   msWCSFreeSubsetObj20()                             */
/*                                                                      */
/*      Frees a wcs20SubsetObj and releases all linked resources.       */
/************************************************************************/

static void msWCSFreeSubsetObj20(wcs20SubsetObjPtr subset)
{
    if (NULL == subset)
    {
        return;
    }
    msFree(subset->axis);
    msFree(subset->crs);
    msFree(subset);
}

/************************************************************************/
/*                   msWCSCreateAxisObj20()                             */
/*                                                                      */
/*      Creates a new wcs20AxisObj and initializes it to standard       */
/*      values.                                                         */
/************************************************************************/

static wcs20AxisObjPtr msWCSCreateAxisObj20()
{
    wcs20AxisObj *axis = (wcs20AxisObjPtr)malloc(sizeof(wcs20AxisObj));
    MS_CHECK_ALLOC(axis, sizeof(wcs20AxisObj), NULL);

    axis->name = NULL;
    axis->size = 0;
    axis->resolution = MS_WCS20_UNBOUNDED;
    axis->resolutionUOM = NULL;
    axis->subset = NULL;

    return axis;
}

/************************************************************************/
/*                   msWCSFreeAxisObj20()                               */
/*                                                                      */
/*      Frees a wcs20AxisObj and releases all linked resources.         */
/************************************************************************/

static void msWCSFreeAxisObj20(wcs20AxisObjPtr axis)
{
    if(NULL == axis)
    {
        return;
    }

    msFree(axis->name);
    msFree(axis->resolutionUOM);
    msWCSFreeSubsetObj20(axis->subset);
    msFree(axis);
}

/************************************************************************/
/*                   msWCSFindAxis20()                                  */
/*                                                                      */
/*      Helper function to retrieve an axis by the name from a params   */
/*      object.                                                         */
/************************************************************************/

static wcs20AxisObjPtr msWCSFindAxis20(wcs20ParamsObjPtr params,
        const char *name)
{
    int i = 0;
    for(i = 0; i < params->numaxes; ++i)
    {
        if(EQUAL(params->axes[i]->name, name))
        {
            return params->axes[i];
        }
    }
    return NULL;
}

/************************************************************************/
/*                   msWCSInsertAxisObj20()                             */
/*                                                                      */
/*      Helper function to insert an axis object into the axes list of  */
/*      a params object.                                                */
/************************************************************************/

static void msWCSInsertAxisObj20(wcs20ParamsObjPtr params, wcs20AxisObjPtr axis)
{
    params->numaxes++;
    params->axes = (wcs20AxisObjPtr*) msSmallRealloc(params->axes,
            sizeof(wcs20AxisObjPtr) * (params->numaxes));
    params->axes[params->numaxes - 1] = axis;
}

/************************************************************************/
/*                   msWCSCreateParamsObj20()                           */
/*                                                                      */
/*      Creates a new wcs20ParamsObj and initializes it to standard     */
/*      values.                                                         */
/************************************************************************/

wcs20ParamsObjPtr msWCSCreateParamsObj20()
{
    wcs20ParamsObjPtr params
        = (wcs20ParamsObjPtr) malloc(sizeof(wcs20ParamsObj));
    MS_CHECK_ALLOC(params, sizeof(wcs20ParamsObj), NULL);

    params->version         = NULL;
    params->request         = NULL;
    params->service         = NULL;
    params->accept_versions = NULL;
    params->sections        = NULL;
    params->updatesequence  = NULL;
    params->ids             = NULL;
    params->width           = 0;
    params->height          = 0;
    params->resolutionX     = MS_WCS20_UNBOUNDED;
    params->resolutionY     = MS_WCS20_UNBOUNDED;
    params->resolutionUnits = NULL;
    params->numaxes         = 0;
    params->axes            = NULL;
    params->format          = NULL;
    params->multipart       = 0;
    params->interpolation   = NULL;
    params->outputcrs       = NULL;
    params->subsetcrs       = NULL;
    params->bbox.minx = params->bbox.miny = -DBL_MAX;
    params->bbox.maxx = params->bbox.maxy =  DBL_MAX;
    params->range_subset    = NULL;
    params->invalid_get_parameters = NULL;

    return params;
}

/************************************************************************/
/*                   msWCSFreeParamsObj20()                             */
/*                                                                      */
/*      Frees a wcs20ParamsObj and releases all linked resources.       */
/************************************************************************/

void msWCSFreeParamsObj20(wcs20ParamsObjPtr params)
{
    if (NULL == params)
    {
        return;
    }

    msFree(params->version);
    msFree(params->request);
    msFree(params->service);
    CSLDestroy(params->accept_versions);
    CSLDestroy(params->sections);
    msFree(params->updatesequence);
    CSLDestroy(params->ids);
    msFree(params->resolutionUnits);
    msFree(params->format);
    msFree(params->interpolation);
    msFree(params->outputcrs);
    msFree(params->subsetcrs);
    while(params->numaxes > 0)
    {
        params->numaxes -= 1;
        msWCSFreeAxisObj20(params->axes[params->numaxes]);
    }
    msFree(params->axes);
    CSLDestroy(params->range_subset);
    CSLDestroy(params->invalid_get_parameters);
    msFree(params);
}

/************************************************************************/
/*                   msWCSParseSubset20()                               */
/*                                                                      */
/*      Parses several string parameters and fills them into the        */
/*      subset object.                                                  */
/************************************************************************/

static int msWCSParseSubset20(wcs20SubsetObjPtr subset, const char *axis,
        const char *crs, const char *min, const char *max)
{
    int ts1, ts2;
    ts1 = ts2 = MS_WCS20_UNDEFINED_VALUE;

    if (subset == NULL)
    {
        return MS_FAILURE;
    }

    if (axis == NULL || strlen(axis) == 0)
    {
        msSetError(MS_WCSERR, "Subset axis is not given.",
                "msWCSParseSubset20()");
        return MS_FAILURE;
    }

    subset->axis = msStrdup(axis);
    if (crs != NULL)
    {
        subset->crs = msStrdup(crs);
    }

    /* Parse first (probably only) part of interval/point;
     * check whether its a time value or a scalar value     */
    ts1 = msWCSParseTimeOrScalar20(&(subset->min), min);
    if (ts1 == MS_WCS20_ERROR_VALUE)
    {
        return MS_FAILURE;
    }

    /* check if its an interval */
    /* if there is a comma, then it is */
    if (max != NULL && strlen(max) > 0)
    {
        subset->operation = MS_WCS20_TRIM;

        /* Parse the second value of the interval */
        ts2 = msWCSParseTimeOrScalar20(&(subset->max), max);
        if (ts2 == MS_WCS20_ERROR_VALUE)
        {
            return MS_FAILURE;
        }

        /* if at least one boundary is defined, use that value */
        if ((ts1 == MS_WCS20_UNDEFINED_VALUE) ^ (ts2
                == MS_WCS20_UNDEFINED_VALUE))
        {
            if (ts1 == MS_WCS20_UNDEFINED_VALUE)
            {
                ts1 = ts2;
            }
        }
        /* if time and scalar values do not fit, throw an error */
        else if (ts1 != MS_WCS20_UNDEFINED_VALUE && ts2
                != MS_WCS20_UNDEFINED_VALUE && ts1 != ts2)
        {
            msSetError(MS_WCSERR,
                    "Interval error: minimum is a %s value, maximum is a %s value",
                    "msWCSParseSubset20()", ts1 ? "time" : "scalar",
                    ts2 ? "time" : "scalar");
            return MS_FAILURE;
        }
        /* if both min and max are unbounded -> throw an error */
        if (subset->min.unbounded && subset->max.unbounded)
        {
            msSetError(MS_WCSERR, "Invalid values: no bounds could be parsed",
                    "msWCSParseSubset20()");
            return MS_FAILURE;
        }
    }
    /* there is no second value, therefore it is a point.
     * consequently set the operation to slice */
    else
    {
        subset->operation = MS_WCS20_SLICE;
        if (ts1 == MS_WCS20_UNDEFINED_VALUE)
        {
            msSetError(MS_WCSERR, "Invalid point value given",
                    "msWCSParseSubset20()");
            return MS_FAILURE;
        }
    }

    subset->timeOrScalar = ts1;

    /* check whether the min is smaller than the max */
    if (subset->operation == MS_WCS20_TRIM)
    {
        if(subset->timeOrScalar == MS_WCS20_SCALAR_VALUE && subset->min.scalar == MS_WCS20_UNBOUNDED)
        {
            subset->min.scalar = -MS_WCS20_UNBOUNDED;
        }

        if (subset->timeOrScalar == MS_WCS20_TIME_VALUE && subset->min.time
                >= subset->max.time)
        {
            msSetError(MS_WCSERR,
                    "Minimum value of subset axis %s is larger than maximum value",
                    "msWCSParseSubset20()", subset->axis);
            return MS_FAILURE;
        }
        if (subset->timeOrScalar == MS_WCS20_SCALAR_VALUE && subset->min.scalar >= subset->max.scalar)
        {
            msSetError(MS_WCSERR,
                    "Minimum value (%f) of subset axis '%s' is larger than maximum value (%f).",
                    "msWCSParseSubset20()", subset->min.scalar, subset->axis, subset->max.scalar);
            return MS_FAILURE;
        }
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseSubsetKVPString20()                      */
/*                                                                      */
/*      Creates a new wcs20SubsetObj, parses a string and fills         */
/*      the parsed values into the object. Returns NULL on failure.     */
/*      Subset string: axis [ , crs ] ( intervalOrPoint )               */
/************************************************************************/

static int msWCSParseSubsetKVPString20(wcs20SubsetObjPtr subset, char *string)
{
    char *axis, *crs, *min, *max;

    axis = string;
    crs = NULL;
    min = NULL;
    max = NULL;

    /* find first '(' */
    min = strchr(string, '(');

    /* if min could not be found, the string is invalid */
    if (min == NULL)
    {
        msSetError(MS_WCSERR, "Invalid axis subset string: '%s'",
                "msWCSParseSubsetKVPString20()", string);
        return MS_FAILURE;
    }
    /* set min to first letter */
    *min = '\0';
    ++min;

    /* cut the trailing ')' */
    if (min[strlen(min) - 1] == ')')
    {
        min[strlen(min) - 1] = '\0';
    }
    /* look if also a max is defined */
    max = strchr(min, ',');
    if (max != NULL)
    {
        *max = '\0';
        ++max;
    }

    /* look if also a crs is defined */
    crs = strchr(axis, ',');
    if (crs != NULL)
    {
        *crs = '\0';
        ++crs;
    }

    return msWCSParseSubset20(subset, axis, crs, min, max);
}

/************************************************************************/
/*                   msWCSParseSizeString20()                           */
/*                                                                      */
/*      Parses a string containing the axis and the size as an integer. */
/*      Size string: axis ( size )                                      */
/************************************************************************/

static int msWCSParseSizeString20(char *string, char *outAxis, size_t axisStringLen, int *outSize)
{
    char *number = NULL;
    char *check = NULL;

    /* find first '(', the character before the number */
    number = strchr(string, '(');

    if(NULL == number)
    {
        msSetError(MS_WCSERR, "Invalid size parameter value.",
                "msWCSParseSize20()");
        return MS_FAILURE;
    }

    /* cut trailing ')' */
    check = strchr(string, ')');
    if(NULL == check)
    {
        msSetError(MS_WCSERR, "Invalid size parameter value.",
                "msWCSParseSize20()");
        return MS_FAILURE;
    }
    *number = '\0';
    ++number;
    *check = '\0';

    strlcpy(outAxis, string, axisStringLen);

    /* parse size value */
    if(msStringParseInteger(number, outSize) != MS_SUCCESS)
    {
        msSetError(MS_WCSERR, "Parameter value '%s' is not a valid integer.",
                "msWCSParseSize20()", number);
        return MS_FAILURE;
    }

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseResolutionString20()                     */
/*                                                                      */
/*      Parses a resolution string and returns the axis, the units of   */
/*      measure and the resolution value.                               */
/*      Subset string: axis ( value )                                   */
/************************************************************************/

static int msWCSParseResolutionString20(char *string,
        char *outAxis, size_t axisStringLen, double *outResolution)
{
    char *number = NULL;
    char *check = NULL;

    /* find brackets */
    number = strchr(string, '(');

    if(NULL == number)
    {
        msSetError(MS_WCSERR, "Invalid resolution parameter value.",
                "msWCSParseSize20()", string);
        return MS_FAILURE;
    }

    /* cut trailing ')' */
    check = strchr(string, ')');
    if(NULL == check)
    {
        msSetError(MS_WCSERR, "Invalid size parameter value.",
                "msWCSParseSize20()");
        return MS_FAILURE;
    }

    *number = '\0';
    ++number;
    *check = '\0';

    strlcpy(outAxis, string, axisStringLen);

    if(msStringParseDouble(number, outResolution) != MS_SUCCESS)
    {
        *outResolution = MS_WCS20_UNBOUNDED;
        msSetError(MS_WCSERR, "Invalid resolution parameter value.",
                "msWCSParseSize20()", string);
        return MS_FAILURE;
    }

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseRequest20_XMLGetCapabilities()           */
/*                                                                      */
/*      Parses a DOM element, representing a GetCapabilities-request    */
/*      to a params object.                                             */
/************************************************************************/

static int msWCSParseRequest20_XMLGetCapabilities(
        xmlNodePtr root, wcs20ParamsObjPtr params)
{
    xmlNodePtr child;
    char *content = NULL;
    XML_FOREACH_CHILD(root, child)
    {
        XML_LOOP_IGNORE_COMMENT_OR_TEXT(child)
        else if (EQUAL((char *)child->name, "AcceptVersions"))
        {
            xmlNodePtr versionNode = NULL;
            XML_FOREACH_CHILD(child, versionNode)
            {
                //for(child = firstChild->children; child != NULL; child = child->next)
                XML_LOOP_IGNORE_COMMENT_OR_TEXT(versionNode);
                XML_ASSERT_NODE_NAME(versionNode, "Version");

                content = (char *)xmlNodeGetContent(versionNode);
                params->accept_versions = CSLAddString(params->accept_versions, content);
                xmlFree(content);
            }
        }
        else if(EQUAL((char *)child->name, "Sections"))
        {
            xmlNodePtr sectionNode = NULL;
            XML_FOREACH_CHILD(child, sectionNode)
            {
                XML_LOOP_IGNORE_COMMENT_OR_TEXT(sectionNode)
                XML_ASSERT_NODE_NAME(sectionNode, "Section");

                content = (char *)xmlNodeGetContent(sectionNode);
                params->sections = CSLAddString(params->sections, content);
                xmlFree(content);
            }
        }
        else if(EQUAL((char *)child->name, "UpdateSequence"))
        {
            params->updatesequence =
                    (char *)xmlNodeGetContent(child);
        }
        else if(EQUAL((char *)child->name, "AcceptFormats"))
        {
            /* Maybe not necessary, since only format is xml.   */
            /* At least ignore it, to not generate an error.    */
        }
        else if(EQUAL((char *)child->name, "AcceptLanguages"))
        {
            /* ignore */
        }
        else
        {
            XML_UNKNOWN_NODE_ERROR(child);
        }
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseRequest20_XMLDescribeCoverage()          */
/*                                                                      */
/*      Parses a DOM element, representing a DescribeCoverage-request   */
/*      to a params object.                                             */
/************************************************************************/

static int msWCSParseRequest20_XMLDescribeCoverage(
        xmlNodePtr root, wcs20ParamsObjPtr params)
{
    xmlNodePtr child;
    int numIds = 0;
    char *id;

    XML_FOREACH_CHILD(root, child)
    {
        XML_LOOP_IGNORE_COMMENT_OR_TEXT(child)
        XML_ASSERT_NODE_NAME(child, "CoverageID");

        /* Node content is the coverage ID */
        id = (char *)xmlNodeGetContent(child);
        if (id == NULL || strlen(id) == 0)
        {
            msSetError(MS_WCSERR, "CoverageID could not be parsed.",
                    "msWCSParseRequest20_XMLDescribeCoverage()");
            return MS_FAILURE;
        }
        /* insert coverage ID into the list */
        ++numIds;
        params->ids = CSLAddString(params->ids, (char *)id);
        xmlFree(id);
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseRequest20_XMLGetCoverage()               */
/*                                                                      */
/*      Parses a DOM element, representing a GetCoverage-request to a   */
/*      params object.                                                  */
/************************************************************************/

static int msWCSParseRequest20_XMLGetCoverage(
        xmlNodePtr root, wcs20ParamsObjPtr params)
{
    xmlNodePtr child;
    int numIds = 0;
    char *id;

    XML_FOREACH_CHILD(root, child)
    {
        XML_LOOP_IGNORE_COMMENT_OR_TEXT(child)
        else if (EQUAL((char *)child->name, "CoverageID"))
        {
            /* Node content is the coverage ID */
            id = (char *)xmlNodeGetContent(child);
            if (id == NULL || strlen(id) == 0)
            {
                msSetError(MS_WCSERR, "CoverageID could not be parsed.",
                        "msWCSParseRequest20_XMLGetCoverage()");
                return MS_FAILURE;
            }

            /* insert coverage ID into the list */
            ++numIds;
            params->ids = CSLAddString(params->ids, (char *)id);
            xmlFree(id);
        }
        else if (EQUAL((char *) child->name, "Format"))
        {
            params->format = (char *)xmlNodeGetContent(child);
        }
        else if (EQUAL((char *) child->name, "Mediatype"))
        {
            char *content = (char *)xmlNodeGetContent(child);
            if(content != NULL && EQUAL(content, "multipart/mixed"))
            {
                params->multipart = MS_TRUE;
            }
            xmlFree(content);
        }
        else if (EQUAL((char *) child->name, "DimensionTrim"))
        {
            wcs20AxisObjPtr axis = NULL;
            wcs20SubsetObjPtr subset = NULL;
            xmlNodePtr node = NULL;
            char *axisName = NULL, *min = NULL, *max = NULL, *crs = NULL;

            /* get strings for axis, min and max */
            XML_FOREACH_CHILD(child, node)
            {
                XML_LOOP_IGNORE_COMMENT_OR_TEXT(node)
                else if (EQUAL((char *)node->name, "Dimension"))
                {
                    if (axisName != NULL)
                    {
                        msSetError(MS_WCSERR,
                                "Parameter 'Dimension' is already set.",
                                "msWCSParseRequest20_XMLGetCoverage()");
                        return MS_FAILURE;
                    }
                    axisName = (char *) xmlNodeGetContent(node);
                    crs = (char *) xmlGetProp(node, BAD_CAST "crs");
                }
                else if (EQUAL((char *)node->name, "trimLow"))
                {
                    min = (char *) xmlNodeGetContent(node);
                }
                else if (EQUAL((char *)node->name, "trimHigh"))
                {
                    max = (char *) xmlNodeGetContent(node);
                }
                else
                {
                    msFree(axisName);
                    msFree(min);
                    msFree(max);
                    msFree(crs);
                    XML_UNKNOWN_NODE_ERROR(node);
                }
            }
            if(NULL == (subset = msWCSCreateSubsetObj20()))
            {
                msFree(axisName);
                msFree(min);
                msFree(max);
                msFree(crs);
                return MS_FAILURE;
            }

            /* min and max have to have a value */
            if(min == NULL )
            {
                min = msStrdup("*");
            }
            if(max == NULL)
            {
                max = msStrdup("*");
            }
            if (msWCSParseSubset20(subset, axisName, crs, min, max)
                    == MS_FAILURE)
            {
                msWCSFreeSubsetObj20(subset);
                return MS_FAILURE;
            }

            if(NULL == (axis = msWCSFindAxis20(params, subset->axis)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    msFree(axisName);
                    msFree(min);
                    msFree(max);
                    msFree(crs);
                    return MS_FAILURE;
                }
                axis->name = msStrdup(subset->axis);
                msWCSInsertAxisObj20(params, axis);
            }

            axis->subset = subset;

            /* cleanup */
            msFree(axisName);
            msFree(min);
            msFree(max);
            msFree(crs);
        }
        else if(EQUAL((char *) child->name, "DimensionSlice"))
        {
            msSetError(MS_WCSERR, "Operation '%s' is not supported by MapServer.",
                    "msWCSParseRequest20_XMLGetCoverage()", (char *)child->name);
            return MS_FAILURE;
        }
        else if(EQUAL((char *) child->name, "Size"))
        {
            wcs20AxisObjPtr axis;
            char *axisName;
            char *content;

            if(NULL == (axisName = (char *) xmlGetProp(child, BAD_CAST "dimension")) )
            {
                msSetError(MS_WCSERR, "Attribute 'dimension' is missing in element 'Size'.",
                        "msWCSParseRequest20_XMLGetCoverage()");
                return MS_FAILURE;
            }

            if(NULL == (axis = msWCSFindAxis20(params, axisName)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    return MS_FAILURE;
                }
                axis->name = msStrdup(axisName);
                msWCSInsertAxisObj20(params, axis);
            }

            content = (char *)xmlNodeGetContent(child);
            if(msStringParseInteger(content, &(axis->size)) != MS_SUCCESS)
            {
                msSetError(MS_WCSERR, "Value of element 'Size' could not "
                        "be parsed to a valid integer.",
                        "msWCSParseRequest20_XMLGetCoverage()");
                return MS_FAILURE;
            }
            xmlFree(content);
        }
        else if(EQUAL((char *) child->name, "Resolution"))
        {
            wcs20AxisObjPtr axis;
            char *axisName;
            char *content;

            if(NULL == (axisName = (char *) xmlGetProp(child, BAD_CAST "dimension")))
            {
                msSetError(MS_WCSERR, "Attribute 'dimension' is missing "
                        "in element 'Resolution'.",
                        "msWCSParseRequest20_XMLGetCoverage()", (char *)child->name);
                return MS_FAILURE;
            }

            if(NULL == (axis = msWCSFindAxis20(params, axisName)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    return MS_FAILURE;
                }
                axis->name = msStrdup(axisName);
                msWCSInsertAxisObj20(params, axis);
            }

            axis->resolutionUOM = (char *) xmlGetProp(child, BAD_CAST "uom");

            content = (char *)xmlNodeGetContent(child);
            if(msStringParseDouble(content, &(axis->resolution)) != MS_SUCCESS)
            {
                msSetError(MS_WCSERR, "Value of element 'Resolution' could not "
                        "be parsed to a valid value.",
                        "msWCSParseRequest20_XMLGetCoverage()");
                xmlFree(content);
                return MS_FAILURE;
            }
            xmlFree(content);
        }
        else if(EQUAL((char *) child->name, "Interpolation"))
        {
            params->interpolation = (char *) xmlNodeGetContent(child);
        }
        else if(EQUAL((char *) child->name, "OutputCRS"))
        {
            params->outputcrs = (char *) xmlNodeGetContent(child);
        }
        else if(EQUAL((char *) child->name, "rangeSubset"))
        {
            xmlNodePtr bandNode = NULL;
            XML_FOREACH_CHILD(child, bandNode)
            {
                char *content = NULL;
                XML_ASSERT_NODE_NAME(bandNode, "band");

                content = (char *)xmlNodeGetContent(bandNode);
                params->range_subset =
                        CSLAddString(params->range_subset, content);
                xmlFree(content);
            }
        }
        else
        {
            XML_UNKNOWN_NODE_ERROR(child);
        }
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSParseRequest20()                              */
/*                                                                      */
/*      Parses a CGI-request to a WCS 20 params object. It is           */
/*      either a POST or a GET request. In case of a POST request       */
/*      the xml content has to be parsed to a DOM structure             */
/*      before the parameters can be extracted.                         */
/************************************************************************/

int msWCSParseRequest20(cgiRequestObj *request, wcs20ParamsObjPtr params)
{
    int i;
    if (params == NULL || request == NULL)
    {
        msSetError(MS_WCSERR, "Internal error.", "msWCSParseRequest20()");
        return MS_FAILURE;
    }

    /* Parse the POST request */
    if (request->type == MS_POST_REQUEST && request->postrequest &&
            strlen(request->postrequest))
    {
#if defined(USE_LIBXML2)
        xmlDocPtr doc = NULL;
        xmlNodePtr root = NULL;
        int ret = MS_SUCCESS;

        msDebug("msWCSParseRequest20(): Parsing request %s\n",
                request->postrequest);

        if (params->version    != NULL
            || params->request != NULL
            || params->service != NULL
            || params->ids     != NULL
            || params->axes    != NULL)
        {
            msSetError(MS_WCSERR, "Params object has already been parsed",
                    "msWCSParseRequest20()");
            return MS_FAILURE;
        }

        /* parse to DOM-Structure and get root element */
        doc = xmlParseMemory(request->postrequest, strlen(request->postrequest));
        if(doc == NULL)
        {
            xmlErrorPtr error = xmlGetLastError();
            msSetError(MS_WCSERR, "XML parsing error: %s",
                    "msWCSParseRequest20()", error->message);
            return MS_FAILURE;
        }
        root = xmlDocGetRootElement(doc);

        /* Get service, version and request from root */
        params->request = msStrdup((char *) root->name);
        params->service = (char *) xmlGetProp(root, BAD_CAST "service");
        params->version = (char *) xmlGetProp(root, BAD_CAST "version");

        if(params->service != NULL && EQUAL(params->service, "WCS"))
        {
            if(EQUAL(params->request, "GetCapabilities"))
            {
                ret = msWCSParseRequest20_XMLGetCapabilities(root, params);
            }
            else if(params->version != NULL && EQUALN(params->version, "2.0", 3))
            {
                if(EQUAL(params->request, "DescribeCoverage"))
                {
                    ret = msWCSParseRequest20_XMLDescribeCoverage(root, params);
                }
                else if(EQUAL(params->request, "GetCoverage"))
                {
                    ret = msWCSParseRequest20_XMLGetCoverage(root, params);
                }
            }
        }
        else
        {
            ret = MS_DONE;
        }

        xmlFreeDoc(doc);
        xmlCleanupParser();

        return ret;

#else /* defined(USE_LIBXML2) */
        /* 'Parse' the xml line by line, only find out Version and Service */
        char **lines = NULL;
        int numLines = 0, i;
        lines = msStringSplit(request->postrequest, '\n', &numLines);
        for(i = 0; i < numLines; ++i)
        {
            char **tokens = NULL;
            int numTokens = 0, j = 0;

            if(EQUALN(lines[i], "<?xml", 5))
                continue;

            tokens = msStringSplit(lines[i], ' ', &numTokens);
            for(j = 0; j < numTokens; ++j)
            {
                if(EQUALN(tokens[j], "SERVICE", strlen("SERVICE")))
                {
                    int k;
                    char *value = strchr(tokens[j], '=');
                    if(value == NULL)
                        continue;
                    ++value;
                    if(value[0] == '"' || value[0] == '\'')
                        ++value;

                    for(k = strlen(value) - 1; k > 0; --k)
                    {
                        if(value[k] == '\'' || value[k] == '"')
                        {
                            value[k] = '\0';
                            break;
                        }
                    }

                    params->service = msStrdup(value);
                }
                else if(EQUALN(tokens[j], "VERSION", strlen("VERSION")))
                {
                    int k;
                    char *value = strchr(tokens[j], '=');
                    if(value == NULL)
                        continue;
                    ++value;
                    if(value[0] == '"' || value[0] == '\'')
                        ++value;

                    for(k = strlen(value) - 1; k > 0; --k)
                    {
                        if(value[k] == '\'' || value[k] == '"')
                        {
                            value[k] = '\0';
                            break;
                        }
                    }

                    params->version = msStrdup(value);
                }
            }
            msFreeCharArray(tokens, numTokens);
        }
        msFreeCharArray(lines, numLines);
        return MS_SUCCESS;
#endif /* defined(USE_LIBXML2) */
    }

    /* Parse the KVP GET request */
    for (i = 0; i < request->NumParams; ++i)
    {
        char *key = NULL, *value = NULL;
        char **tokens;
        int num, j;
        key = request->ParamNames[i];
        value = request->ParamValues[i];

        if (EQUAL(key, "VERSION"))
        {
            if (params->version)
            {
                msSetError(MS_WCSERR, "Parameter 'Version' is already set.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            params->version = msStrdup(value);
        }
        else if (EQUAL(key, "REQUEST"))
        {
            if (params->request)
            {
                msSetError(MS_WCSERR, "Parameter 'Request' is already set.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            params->request = msStrdup(value);
        }
        else if (EQUAL(key, "SERVICE"))
        {
            if (params->service)
            {
                msSetError(MS_WCSERR, "Parameter 'Service' is already set.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            params->service = msStrdup(value);
        }
        else if (EQUAL(key, "ACCEPTVERSIONS"))
        {
            tokens = msStringSplit(value, ',', &num);
            for(j = 0; j < num; ++j)
            {
                params->accept_versions =
                        CSLAddString(params->accept_versions, tokens[j]);
            }
            msFreeCharArray(tokens, num);
        }
        else if (EQUAL(key, "SECTIONS"))
        {
            tokens = msStringSplit(value, ',', &num);
            for(j = 0; j < num; ++j)
            {
                params->sections =
                        CSLAddString(params->sections, tokens[j]);
            }
            msFreeCharArray(tokens, num);
        }
        else if (EQUAL(key, "UPDATESEQUENCE"))
        {
            params->updatesequence = msStrdup(value);
        }
        else if (EQUAL(key, "ACCEPTFORMATS"))
        {
            /* ignore */
        }
        else if (EQUAL(key, "ACCEPTLANGUAGES"))
        {
            /* ignore */
        }
        else if (EQUAL(key, "COVERAGEID"))
        {
            if (params->ids != NULL)
            {
                msSetError(MS_WCSERR, "Parameter 'CoverageID' is already set. "
                        "For multiple IDs use a comma separated list.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            tokens = msStringSplit(value, ',', &num);
            params->ids = (char **) msSmallCalloc(num + 1, sizeof(char *));
            for (j = 0; j < num; ++j)
            {
                params->ids[j] = msStrdup(tokens[j]);
            }
            msFreeCharArray(tokens, num);
        }
        else if (EQUAL(key, "FORMAT"))
        {
            params->format = msStrdup(value);
        }
        else if (EQUAL(key, "MEDIATYPE"))
        {
            if(EQUAL(value, "multipart/mixed"))
            {
                params->multipart = MS_TRUE;
            }
        }
        else if (EQUAL(key, "INTERPOLATION"))
        {
            params->interpolation = msStrdup(value);
        }
        else if (EQUAL(key, "OUTPUTCRS"))
        {
            params->outputcrs = msStrdup(value);
        }
        else if (EQUALN(key, "SIZE", 4))
        {
            wcs20AxisObjPtr axis = NULL;
            char axisName[500];
            int size = 0;

            if(msWCSParseSizeString20(value, axisName, sizeof(axisName), &size) == MS_FAILURE)
            {
                return MS_FAILURE;
            }

            if(NULL == (axis = msWCSFindAxis20(params, axisName)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    return MS_FAILURE;
                }
                axis->name = msStrdup(axisName);
                msWCSInsertAxisObj20(params, axis);
            }

            /* check if the size of the axis is already set */
            if(axis->size != 0)
            {
                msSetError(MS_WCSERR, "The size of the axis is already set.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            axis->size = size;
        }
        else if (EQUALN(key, "RESOLUTION", 10))
        {
            wcs20AxisObjPtr axis = NULL;
            char axisName[500];
            double resolution = 0;

            if(msWCSParseResolutionString20(value, axisName, sizeof(axisName), &resolution) == MS_FAILURE)
            {
                return MS_FAILURE;
            }

            /* check if axis object already exists, otherwise create a new one */
            if(NULL == (axis = msWCSFindAxis20(params, axisName)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    return MS_FAILURE;
                }
                axis->name = msStrdup(axisName);
                msWCSInsertAxisObj20(params, axis);
            }

            /* check if the resolution of the axis is already set */
            if(axis->resolution != MS_WCS20_UNBOUNDED)
            {
                msSetError(MS_WCSERR, "The resolution of the axis is already set.",
                        "msWCSParseRequest20()");
                return MS_FAILURE;
            }
            axis->resolution = resolution;
        }
        else if (EQUALN(key, "SUBSET", 6))
        {
            wcs20AxisObjPtr axis = NULL;
            wcs20SubsetObjPtr subset = msWCSCreateSubsetObj20();
            if(NULL == subset)
            {
                return MS_FAILURE;
            }
            if (msWCSParseSubsetKVPString20(subset, value) == MS_FAILURE)
            {
                msWCSFreeSubsetObj20(subset);
                return MS_FAILURE;
            }

            if(NULL == (axis = msWCSFindAxis20(params, subset->axis)))
            {
                if(NULL == (axis = msWCSCreateAxisObj20()))
                {
                    return MS_FAILURE;
                }
                axis->name = msStrdup(subset->axis);
                msWCSInsertAxisObj20(params, axis);
            }

            if(NULL != axis->subset)
            {
                msSetError(MS_WCSERR, "The axis '%s' is already subsetted.",
                        "msWCSParseRequest20()", axis->name);
                msWCSFreeSubsetObj20(subset);
                return MS_FAILURE;
            }
            axis->subset = subset;
        }
        else if(EQUAL(key, "RANGESUBSET"))
        {
            tokens = msStringSplit(value, ',', &num);
            for(j = 0; j < num; ++j)
            {
                params->range_subset =
                        CSLAddString(params->range_subset, tokens[j]);
            }
            msFreeCharArray(tokens, num);
        }
        /* insert other mapserver internal, to be ignored parameters here */
        else if(EQUAL(key, "MAP"))
        {
            continue;
        }
        else
        {
            /* append unknown parameter to the list */
            params->invalid_get_parameters
                = CSLAddString(params->invalid_get_parameters, key);
        }
    }



    return MS_SUCCESS;
}

#if defined(USE_LIBXML2)

/************************************************************************/
/*                   msWCSValidateAndFindSubsets20()                    */
/*                                                                      */
/*      Iterates over every axis in the parameters and checks if the    */
/*      axis name is in any string list. If found, but there already is */
/*      a sample found for this axis, an Error is returned. Also if no  */
/*      axis is found for a given axis, an error is returned.           */
/************************************************************************/
static int msWCSValidateAndFindAxes20(
        wcs20ParamsObjPtr params,
        char*** validAxisNames,
        int numAxis,
        wcs20AxisObjPtr outAxes[])
{
    int iParamAxis, iAcceptedAxis, iName, i;

    for(i = 0; i < numAxis; ++i)
    {
        outAxes[i] = NULL;
    }

    /* iterate over all subsets */
    for(iParamAxis = 0; iParamAxis < params->numaxes; ++iParamAxis)
    {
        int found = 0;

        /* check if subset is valid */
        if(params->axes[iParamAxis]->subset != NULL)
        {
            if(params->axes[iParamAxis]->subset->timeOrScalar == MS_WCS20_TIME_VALUE)
            {
                msSetError(MS_WCSERR, "Time values for subsets are not supported. ",
                        "msWCSCreateBoundingBox20()");
                return MS_FAILURE;
            }
            if(params->axes[iParamAxis]->subset->operation == MS_WCS20_SLICE)
            {
                msSetError(MS_WCSERR, "Subset operation 'slice' is not supported.",
                        "msWCSCreateBoundingBox20()");
                return MS_FAILURE;
            }
        }

        /* iterate over all given axes */
        for(iAcceptedAxis = 0; iAcceptedAxis < numAxis; ++iAcceptedAxis )
        {
            /* iterate over all possible names for the current axis */
            for(iName = 0; validAxisNames[iAcceptedAxis][iName] != NULL ; ++iName)
            {
                /* compare axis name with current possible name */
                if(EQUAL(params->axes[iParamAxis]->name, validAxisNames[iAcceptedAxis][iName]))
                {
                    /* if there is already a sample for the axis, throw error */
                    if(outAxes[iAcceptedAxis] != NULL)
                    {
                        msSetError(MS_WCSERR, "The axis with the name '%s' corresponds "
                                "to the same axis as the subset with the name '%s'.",
                                "msWCSValidateAndFindSubsets20()",
                                outAxes[iAcceptedAxis]->name, params->axes[iParamAxis]->name);
                        return MS_FAILURE;
                    }

                    /* if match is found, save it */
                    outAxes[iAcceptedAxis] = params->axes[iParamAxis];
                    found = 1;
                    break;
                }
            }
            if (found)
            {
                break;
            }
        }

        /* no valid representation for current subset found */
        /* exit and throw error                             */
        if(found == 0)
        {
            msSetError(MS_WCSERR, "Invalid subset axis '%s'.",
                    "msWCSValidateAndFindSubsets20()", params->axes[iParamAxis]->name);
            return MS_FAILURE;
        }
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSPrepareNamespaces20()                         */
/*                                                                      */
/*      Inserts namespace definitions into the root node of a DOM       */
/*      structure.                                                      */
/************************************************************************/

static void msWCSPrepareNamespaces20(xmlDocPtr pDoc, xmlNodePtr psRootNode, mapObj* map)
{
    xmlNsPtr psXsiNs;
    char *schemaLocation = NULL;
    char *xsi_schemaLocation = NULL;

    xmlSetNs(psRootNode, xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_WCS_20_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX));

    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_OWS_20_NAMESPACE_URI,        BAD_CAST MS_OWSCOMMON_OWS_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_URI,           BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_PREFIX );
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_URI,       BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_URI,     BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_WCS_20_NAMESPACE_URI,        BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_GML_32_NAMESPACE_URI,        BAD_CAST MS_OWSCOMMON_GML_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_GMLCOV_10_NAMESPACE_URI,     BAD_CAST MS_OWSCOMMON_GMLCOV_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_SWE_20_NAMESPACE_URI,        BAD_CAST MS_OWSCOMMON_SWE_NAMESPACE_PREFIX);

    psXsiNs = xmlSearchNs(pDoc, psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_PREFIX);

    schemaLocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );
    xsi_schemaLocation = msStrdup(MS_OWSCOMMON_WCS_20_NAMESPACE_URI);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, " ");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, schemaLocation);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, MS_OWSCOMMON_WCS_20_SCHEMAS_LOCATION);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, " ");

    xmlNewNsProp(psRootNode, psXsiNs, BAD_CAST "schemaLocation", BAD_CAST xsi_schemaLocation);

    msFree(schemaLocation);
    msFree(xsi_schemaLocation);
}

/************************************************************************/
/*                   msWCSGetFormatList20()                             */
/*                                                                      */
/*      Copied from mapwcs.c.                                           */
/************************************************************************/

static char *msWCSGetFormatsList20( mapObj *map, layerObj *layer )
{
    char *format_list = msStrdup("");
    char **tokens = NULL, **formats = NULL;
    int  i, numtokens = 0, numformats;
    const char *value;

    /* -------------------------------------------------------------------- */
    /*      Parse from layer metadata.                                      */
    /* -------------------------------------------------------------------- */
    if( layer != NULL
        && (value = msOWSGetEncodeMetadata( &(layer->metadata),"COM","formats",
                                            NULL )) != NULL )
    {
        tokens = msStringSplit(value, ' ', &numtokens);
    }

    /* -------------------------------------------------------------------- */
    /*      Or generate from all configured raster output formats that      */
    /*      look plausible.                                                 */
    /* -------------------------------------------------------------------- */
    else
    {
        tokens = (char **) msSmallCalloc(map->numoutputformats,sizeof(char*));
        for( i = 0; i < map->numoutputformats; i++ )
        {
            switch( map->outputformatlist[i]->renderer )
            {
            /* seemingly normal raster format */
            case MS_RENDER_WITH_GD:
            case MS_RENDER_WITH_AGG:
            case MS_RENDER_WITH_RAWDATA:
                tokens[numtokens++] = msStrdup(map->outputformatlist[i]->name);
                break;
            /* rest of formats aren't really WCS compatible */
            default:
                break;
            }
        }
    }

    /* -------------------------------------------------------------------- */
    /*      Convert outputFormatObj names into mime types and remove        */
    /*      duplicates.                                                     */
    /* -------------------------------------------------------------------- */
    numformats = 0;
    formats = (char **) msSmallCalloc(sizeof(char*),numtokens);

    for( i = 0; i < numtokens; i++ )
    {
        int format_i, j;
        const char *mimetype;

        for( format_i = 0; format_i < map->numoutputformats; format_i++ )
        {
            if( EQUAL(map->outputformatlist[format_i]->name, tokens[i]) )
                break;
        }

        if( format_i == map->numoutputformats )
        {
            msDebug("Failed to find outputformat info on format '%s', ignore.\n",
                    tokens[i] );
            continue;
        }

        mimetype = map->outputformatlist[format_i]->mimetype;
        if( mimetype == NULL || strlen(mimetype) == 0 )
        {
            msDebug("No mimetime for format '%s', ignoring.\n",
                    tokens[i] );
            continue;
        }

        for( j = 0; j < numformats; j++ )
        {
            if( EQUAL(mimetype,formats[j]) )
                break;
        }

        if( j < numformats )
        {
            msDebug( "Format '%s' ignored since mimetype '%s' duplicates another outputFormatObj.\n",
                     tokens[i], mimetype );
            continue;
        }

        formats[numformats++] = msStrdup(mimetype);
    }

    msFreeCharArray(tokens,numtokens);

    /* -------------------------------------------------------------------- */
    /*      Turn mimetype list into comma delimited form for easy use       */
    /*      with xml functions.                                             */
    /* -------------------------------------------------------------------- */
    for(i = 0; i < numformats; i++)
    {
        if(i > 0)
        {
            format_list = msStringConcatenate(format_list, (char *) ",");
        }
        format_list = msStringConcatenate(format_list, formats[i]);
    }
    msFreeCharArray(formats,numformats);

    return format_list;
}

/************************************************************************/
/*                   msWCSCommon20_CreateBoundedBy()                    */
/*                                                                      */
/*      Inserts the BoundedBy section into an existing DOM structure.   */
/************************************************************************/

static void msWCSCommon20_CreateBoundedBy(layerObj *layer, wcs20coverageMetadataObjPtr cm,
        xmlNsPtr psGmlNs, xmlNodePtr psRoot, projectionObj *projection)
{
    xmlNodePtr psBoundedBy, psEnvelope;
    char lowerCorner[100], upperCorner[100], axisLabels[100], uomLabels[100];

    psBoundedBy = xmlNewChild( psRoot, psGmlNs, BAD_CAST "boundedBy", NULL);
    {
        psEnvelope = xmlNewChild(psBoundedBy, psGmlNs, BAD_CAST "Envelope", NULL);
        {
            xmlNewProp(psEnvelope, BAD_CAST "srsName", BAD_CAST cm->srs_uri);

            if(projection->proj != NULL && pj_is_latlong(projection->proj))
            {
                strlcpy(axisLabels, "lat long", sizeof(axisLabels));
                strlcpy(uomLabels, "deg deg", sizeof(uomLabels));
            }
            else
            {
                strlcpy(axisLabels, "x y", sizeof(axisLabels));
                strlcpy(uomLabels, "m m", sizeof(uomLabels));
            }
            xmlNewProp(psEnvelope, BAD_CAST "axisLabels", BAD_CAST axisLabels);
            xmlNewProp(psEnvelope, BAD_CAST "uomLabels", BAD_CAST uomLabels);
            xmlNewProp(psEnvelope, BAD_CAST "srsDimension", BAD_CAST "2");

            snprintf(lowerCorner, sizeof(lowerCorner), "%.15g %.15g", cm->extent.minx, cm->extent.miny);
            snprintf(upperCorner, sizeof(upperCorner), "%.15g %.15g", cm->extent.maxx, cm->extent.maxy);

            xmlNewChild(psEnvelope, psGmlNs, BAD_CAST "lowerCorner", BAD_CAST lowerCorner);
            xmlNewChild(psEnvelope, psGmlNs, BAD_CAST "upperCorner", BAD_CAST upperCorner);
        }
    }
}

/************************************************************************/
/*                   msWCSCommon20_CreateDomainSet()                    */
/*                                                                      */
/*      Inserts the DomainSet section into an existing DOM structure.   */
/************************************************************************/

static void msWCSCommon20_CreateDomainSet(layerObj* layer, wcs20coverageMetadataObjPtr cm,
        xmlNsPtr psGmlNs, xmlNodePtr psRoot, projectionObj *projection)
{
    xmlNodePtr psDomainSet, psGrid, psLimits, psGridEnvelope, psOrigin,
        psPos, psOffsetX, psOffsetY;
    char low[100], high[100], id[100], point[100], resx[100], resy[100], axisLabels[100];

    psDomainSet = xmlNewChild( psRoot, psGmlNs, BAD_CAST "domainSet", NULL);
    {
        psGrid = xmlNewChild(psDomainSet, psGmlNs, BAD_CAST "RectifiedGrid", NULL);
        {
            xmlNewProp(psGrid, BAD_CAST "dimension", BAD_CAST "2");
            snprintf(id, sizeof(id), "grid_%s", layer->name);
            xmlNewNsProp(psGrid, psGmlNs, BAD_CAST "id", BAD_CAST id);

            psLimits = xmlNewChild(psGrid, psGmlNs, BAD_CAST "limits", NULL);
            {
                psGridEnvelope = xmlNewChild(psLimits, psGmlNs, BAD_CAST "GridEnvelope", NULL);
                {
                    strlcpy(low, "0 0", sizeof(low));
                    snprintf(high, sizeof(high), "%d %d", cm->xsize - 1, cm->ysize - 1);

                    xmlNewChild(psGridEnvelope, psGmlNs, BAD_CAST "low", BAD_CAST low);
                    xmlNewChild(psGridEnvelope, psGmlNs, BAD_CAST "high", BAD_CAST high);
                }
            }
            
            if(pj_is_latlong(projection->proj))
            {
                strlcpy(axisLabels, "lat long", sizeof(axisLabels));
            }
            else
            {
                strlcpy(axisLabels, "x y", sizeof(axisLabels));
            }

            xmlNewChild(psGrid, psGmlNs, BAD_CAST "axisLabels", BAD_CAST axisLabels);

            psOrigin = xmlNewChild(psGrid, psGmlNs, BAD_CAST "origin", NULL);
            {
                snprintf(point, sizeof(point), "%f %f", cm->extent.minx, cm->extent.miny);
                psOrigin = xmlNewChild(psOrigin, psGmlNs, BAD_CAST "Point", NULL);
                snprintf(id, sizeof(id), "grid_origin_%s", layer->name);
                xmlNewNsProp(psOrigin, psGmlNs, BAD_CAST "id", BAD_CAST id);
                xmlNewProp(psOrigin, BAD_CAST "srsName", BAD_CAST cm->srs_uri);

                psPos = xmlNewChild(psOrigin, psGmlNs, BAD_CAST "pos", BAD_CAST point);
            }
            snprintf(resx, sizeof(resx), "%f 0", cm->xresolution);
            snprintf(resy, sizeof(resy), "0 %f", cm->yresolution);
            psOffsetX = xmlNewChild(psGrid, psGmlNs, BAD_CAST "offsetVector", BAD_CAST resx);
            xmlNewProp(psOffsetX, BAD_CAST "srsName", BAD_CAST cm->srs_uri);
            psOffsetY = xmlNewChild(psGrid, psGmlNs, BAD_CAST "offsetVector", BAD_CAST resy);
            xmlNewProp(psOffsetY, BAD_CAST "srsName", BAD_CAST cm->srs_uri);
        }
    }
}

/************************************************************************/
/*                   msWCSCommon20_CreateRangeType()                    */
/*                                                                      */
/*      Inserts the RangeType section into an existing DOM structure.   */
/************************************************************************/

static void msWCSCommon20_CreateRangeType(layerObj* layer, wcs20coverageMetadataObjPtr cm,
        xmlNsPtr psGmlNs, xmlNsPtr psGmlcovNs, xmlNsPtr psSweNs, xmlNsPtr psXLinkNs, xmlNodePtr psRoot)
{
    xmlNodePtr psRangeType, psDataRecord, psField, psQuantity,
        psUom, psConstraint, psAllowedValues = NULL/*, psNilValues = NULL*/;
    char * value;
    int i;
    psRangeType = xmlNewChild( psRoot, psGmlcovNs, BAD_CAST "rangeType", NULL);
    psDataRecord  = xmlNewChild(psRangeType, psSweNs, BAD_CAST "DataRecord", NULL);

    /* iterate over every band */
    for(i = 0; i < cm->numbands && i < 10; ++i)
    {
        /* add field tag */
        psField = xmlNewChild(psDataRecord, psSweNs, BAD_CAST "field", NULL);

        if(cm->bands[i].interpretation != NULL)
        {
            xmlNewProp(psField, BAD_CAST "name", BAD_CAST cm->bands[i].interpretation);
        }
        else
        {
            xmlNewProp(psField, BAD_CAST "name", BAD_CAST "band");
        }
        /* add Quantity tag */
        psQuantity = xmlNewChild(psField, psSweNs, BAD_CAST "Quantity", NULL);
        if(cm->bands[i].definition != NULL)
        {
            xmlNewProp(psQuantity, BAD_CAST "definition", BAD_CAST cm->bands[i].definition);
        }
        if(cm->bands[i].description != NULL)
        {
            xmlNewChild(psQuantity, psSweNs, BAD_CAST "description", BAD_CAST cm->bands[i].description);
        }

        psUom = xmlNewChild(psQuantity, psSweNs, BAD_CAST "uom", NULL);
        if(cm->bands[i].uom != NULL)
        {
            xmlNewProp(psUom, BAD_CAST "code", BAD_CAST cm->bands[i].uom);
        }
        else
        {
            xmlNewProp(psUom, BAD_CAST "code", BAD_CAST "W.m-2.Sr-1");
        }

        /* add constraint */
        psConstraint = xmlNewChild(psQuantity, psSweNs, BAD_CAST "constraint", NULL);
        
        {
            char interval[100];
            psAllowedValues = xmlNewChild(psConstraint, psSweNs, BAD_CAST "AllowedValues", NULL);
            switch(cm->imagemode)
            {
                case MS_IMAGEMODE_BYTE:
                    snprintf(interval, sizeof(interval), "%d %d", 0, 255);
                    break;
                case MS_IMAGEMODE_INT16:
                    snprintf(interval, sizeof(interval), "%d %d", 0, USHRT_MAX);
                    break;
                case MS_IMAGEMODE_FLOAT32:
                    snprintf(interval, sizeof(interval), "%.5f %.5f", -FLT_MAX, FLT_MAX);
                    break;
            }
            xmlNewChild(psAllowedValues, psSweNs, BAD_CAST "interval", BAD_CAST interval);
            if((value  = msOWSGetEncodeMetadata(&(layer->metadata), "COM", "band_significant_figures", NULL)) != NULL)
            {
                xmlNewChild(psAllowedValues, psSweNs, BAD_CAST "significantFigures", BAD_CAST value);
            }
        }

        /* if there are given nilvalues -> add them to the first field */
        /* all other fields get a reference to these */
        /* TODO: look up specs for nilValue */
        /*if(psNilValues == NULL && numNilValues > 0)
        {
            int j;
            char id[100];
            psNilValues = xmlNewChild(
                xmlNewChild(psQuantity, psSweNs, BAD_CAST "nilValues", NULL),
                psSweNs, BAD_CAST "NilValues", NULL);
            snprintf(id, sizeof(id), "NIL_VALUES_%s", layer->name);
            xmlNewNsProp(psNilValues, psGmlNs, BAD_CAST "id", BAD_CAST id);
            for(j = 0; j < numNilValues; ++j)
            {
                xmlNodePtr psTemp =
                    xmlNewChild(psNilValues, psSweNs, BAD_CAST "nilValue", BAD_CAST nilValues[j]);
                if(j < numNilValueReasons)
                    xmlNewProp(psTemp, BAD_CAST "reason", BAD_CAST nilValueReasons[j]);
            }
        }
        else if(numNilValues > 0)
        {
            char href[100];
            xmlNodePtr psTemp =
                xmlNewChild(psQuantity, psSweNs, BAD_CAST "nilValues", NULL);
            snprintf(href, sizeof(href), "#NIL_VALUES_%s", layer->name);
            xmlNewNsProp(psTemp, psXLinkNs, BAD_CAST "href", BAD_CAST href);
        }*/
    }
}

/************************************************************************/
/*                   msWCSWriteDocument20()                             */
/*                                                                      */
/*      Writes out an xml structure to the stream.                      */
/************************************************************************/

static int msWCSWriteDocument20(mapObj* map, xmlDocPtr psDoc)
{
    xmlChar *buffer = NULL;
    int size = 0;
    msIOContext *context = NULL;

    const char *encoding = msOWSLookupMetadata(&(map->web.metadata), "CO", "encoding");

    if( msIO_needBinaryStdout() == MS_FAILURE )
    {
        return MS_FAILURE;
    }

    if (encoding)
    {
        msIO_printf("Content-type: text/xml; charset=%s%c%c", encoding,10,10);
    }
    else
    {
        msIO_printf("Content-type: text/xml%c%c",10,10);
    }

    context = msIO_getHandler(stdout);

    xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, (encoding ? encoding : "ISO-8859-1"), 1);
    msIO_contextWrite(context, buffer, size);
    xmlFree(buffer);

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSWriteFile20()                                 */
/*                                                                      */
/*      Writes an image object to the stream. If multipart is set,      */
/*      then content sections are inserted.                             */
/************************************************************************/

static int msWCSWriteFile20(mapObj* map, imageObj* image, wcs20ParamsObjPtr params, int multipart)
{
    int status;
    char* filename = NULL;
    const char *fo_filename;
    int i;

    fo_filename = msGetOutputFormatOption( image->format, "FILENAME", NULL );

    /* -------------------------------------------------------------------- */
    /*      Fetch the driver we will be using and check if it supports      */
    /*      VSIL IO.                                                        */
    /* -------------------------------------------------------------------- */
#ifdef GDAL_DCAP_VIRTUALIO
    if( EQUALN(image->format->driver,"GDAL/",5) )
    {
        GDALDriverH hDriver;
        const char *pszExtension = image->format->extension;

        msAcquireLock( TLOCK_GDAL );
        hDriver = GDALGetDriverByName( image->format->driver+5 );
        if( hDriver == NULL )
        {
            msReleaseLock( TLOCK_GDAL );
            msSetError( MS_MISCERR,
                        "Failed to find %s driver.",
                        "msWCSWriteFile20()",
                        image->format->driver+5 );
            return msWCSException(map, "mapserv", "NoApplicableCode",
                                  params->version);
        }

        if( pszExtension == NULL )
            pszExtension = "img.tmp";

        if( GDALGetMetadataItem( hDriver, GDAL_DCAP_VIRTUALIO, NULL )
            != NULL )
        {
            if( fo_filename )
                filename = msStrdup(CPLFormFilename("/vsimem/wcsout",
                                                    fo_filename,NULL));
            else
                filename = msStrdup(CPLFormFilename("/vsimem/wcsout", 
                                                    "out", pszExtension ));

            /*            CleanVSIDir( "/vsimem/wcsout" ); */

            msReleaseLock( TLOCK_GDAL );
            status = msSaveImage(map, image, filename);
            if( status != MS_SUCCESS )
            {
                msSetError(MS_MISCERR, "msSaveImage() failed",
                           "msWCSWriteFile20()");
                return msWCSException20(map, "mapserv", "NoApplicableCode",
                                        params->version);
            }
        }
        msReleaseLock( TLOCK_GDAL );
    }
#endif

    /* -------------------------------------------------------------------- */
    /*      If we weren't able to write data under /vsimem, then we just    */
    /*      output a single "stock" filename.                               */
    /* -------------------------------------------------------------------- */
    if( filename == NULL )
    {
        if(multipart)
        {
            msIO_fprintf( stdout, "--wcs\n" );
        }
        msIO_fprintf(
            stdout,
            "Content-Type: %s\n"
            "Content-Description: coverage data\n"
            "Content-Transfer-Encoding: binary\n",
            MS_IMAGE_MIME_TYPE(map->outputformat));

        if( fo_filename != NULL )
            msIO_fprintf( stdout, 
                "Content-ID: coverage/%s\n"
                "Content-Disposition: attachment; filename=%s%c%c",
                fo_filename,
                fo_filename,
                10, 10 );
        else
            msIO_fprintf( stdout, 
                "Content-ID: coverage/wcs.%s\n"
                "Content-Disposition: INLINE%c%c",
                MS_IMAGE_EXTENSION(map->outputformat),
                10, 10 );

        status = msSaveImage(map, image, NULL);
        if( status != MS_SUCCESS )
        {
            msSetError( MS_MISCERR, "msSaveImage() failed", "msWCSWriteFile20()");
            return msWCSException(map, "mapserv", "NoApplicableCode", params->version);
        }
        if(multipart)
            msIO_fprintf( stdout, "\n--wcs--%c%c", 10, 10 );
        return MS_SUCCESS;
    }

    /* -------------------------------------------------------------------- */
    /*      When potentially listing multiple files, we take great care     */
    /*      to identify the "primary" file and list it first.  In fact      */
    /*      it is the only file listed in the coverages document.           */
    /* -------------------------------------------------------------------- */
#ifdef GDAL_DCAP_VIRTUALIO
    {
        char **all_files = CPLReadDir( "/vsimem/wcsout" );
        int count = CSLCount(all_files);

        if( msIO_needBinaryStdout() == MS_FAILURE )
            return MS_FAILURE;

        msAcquireLock( TLOCK_GDAL );
        for( i = count-1; i >= 0; i-- )
        {
            const char *this_file = all_files[i];

            if( EQUAL(this_file,".") || EQUAL(this_file,"..") )
            {
                all_files = CSLRemoveStrings( all_files, i, 1, NULL );
                continue;
            }

            if( i > 0 && EQUAL(this_file,CPLGetFilename(filename)) )
            {
                all_files = CSLRemoveStrings( all_files, i, 1, NULL );
                all_files = CSLInsertString(all_files,0,CPLGetFilename(filename));
                i++;
            }
        }

        /* -------------------------------------------------------------------- */
        /*      Dump all the files in the memory directory as mime sections.    */
        /* -------------------------------------------------------------------- */
        count = CSLCount(all_files);

        if(count > 1 && multipart == MS_FALSE)
        {
            msDebug( "msWCSWriteFile20(): force multipart output without gml summary because we have multiple files in the result.\n" );

            multipart = MS_TRUE;
            msIO_printf(
                "Content-Type: multipart/mixed; boundary=wcs%c%c", 10, 10);
        }

        for( i = 0; i < count; i++ )
        {
            const char *mimetype = NULL;
            FILE *fp;
            unsigned char block[4000];
            int bytes_read;

            if( i == 0
                && !EQUAL(MS_IMAGE_MIME_TYPE(map->outputformat), "unknown") )
                mimetype = MS_IMAGE_MIME_TYPE(map->outputformat);

            if( mimetype == NULL )
                mimetype = "application/octet-stream";
            if(multipart)
            {
                msIO_fprintf( stdout, "--wcs\n" );
            }

            msIO_fprintf(
                stdout,
                "Content-Type: %s\n"
                "Content-Description: coverage data\n"
                "Content-Transfer-Encoding: binary\n"
                "Content-ID: coverage/%s\n"
                "Content-Disposition: attachment; filename=%s%c%c",
                mimetype,
                all_files[i],
                all_files[i],
                10, 10 );

            fp = VSIFOpenL(
                CPLFormFilename("/vsimem/wcsout", all_files[i], NULL),
                "rb" );
            if( fp == NULL )
            {
                msReleaseLock( TLOCK_GDAL );
                msSetError( MS_MISCERR,
                            "Failed to open %s for streaming to stdout.",
                            "msWCSWriteFile20()", all_files[i] );
                return MS_FAILURE;
            }

            while( (bytes_read = VSIFReadL(block, 1, sizeof(block), fp)) > 0 )
                msIO_fwrite( block, 1, bytes_read, stdout );

            VSIFCloseL( fp );

            VSIUnlink( all_files[i] );
        }

        msFree(filename);
        CSLDestroy( all_files );
        msReleaseLock( TLOCK_GDAL );
        if(multipart)
            msIO_fprintf( stdout, "\n--wcs--%c%c", 10, 10 );
        return MS_SUCCESS;
    }
#endif /* def GDAL_DCAP_VIRTUALIO */

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCoverageMetadata20()                       */
/*                                                                      */
/*      Inits a coverageMetadataObj. Uses msWCSGetCoverageMetadata()    */
/*      but exchanges the SRS URN by an URI for compliancy with 2.0.    */
/************************************************************************/

static int msWCSGetCoverageMetadata20(layerObj *layer, wcs20coverageMetadataObj *cm)
{
    char  *srs_uri = NULL;
    int i = 0;
    if ( msCheckParentPointer(layer->map,"map") == MS_FAILURE )
        return MS_FAILURE;

    if((cm->srs = msOWSGetEPSGProj(&(layer->projection),
            &(layer->metadata), "COM", MS_TRUE)) == NULL)
    {
        if((cm->srs = msOWSGetEPSGProj(&(layer->map->projection),
                &(layer->map->web.metadata), "COM", MS_TRUE)) == NULL)
        {
            msSetError(MS_WCSERR, "Unable to determine the SRS for this layer, "
                    "no projection defined and no metadata available.",
                    "msWCSGetCoverageMetadata20()");
            return MS_FAILURE;
        }
    }

    /* -------------------------------------------------------------------- */
    /*      Get the SRS in uri format.                                      */
    /* -------------------------------------------------------------------- */
    if((srs_uri = msOWSGetProjURI(&(layer->projection), &(layer->metadata),
        "COM", MS_TRUE)) == NULL)
    {
        srs_uri = msOWSGetProjURI(&(layer->map->projection),
                &(layer->map->web.metadata), "COM", MS_TRUE);
    }

    if( srs_uri != NULL )
    {
        if( strlen(srs_uri) > sizeof(cm->srs_uri) - 1 )
        {
            msSetError(MS_WCSERR, "SRS URI too long!",
                    "msWCSGetCoverageMetadata()");
            return MS_FAILURE;
        }

        strlcpy( cm->srs_uri, srs_uri, sizeof(cm->srs_uri) );
        msFree( srs_uri );
    }
    else
    {
        cm->srs_uri[0] = '\0';
    }

    /* setup nilvalues */
    cm->numnilvalues = 0;
    cm->nilvalues = NULL;
    cm->nilvalues_reasons = NULL;
    cm->native_format = NULL;

    /* -------------------------------------------------------------------- */
    /*      If we have "virtual dataset" metadata on the layer, then use    */
    /*      that in preference to inspecting the file(s).                   */
    /*      We require extent and either size or resolution.                */
    /* -------------------------------------------------------------------- */
    if( msOWSLookupMetadata(&(layer->metadata), "COM", "extent") != NULL
        && (msOWSLookupMetadata(&(layer->metadata), "COM", "resolution") != NULL
        || msOWSLookupMetadata(&(layer->metadata), "COM", "size") != NULL) )
    {
        const char *value;

        /* get extent */
        cm->extent.minx = 0.0;
        cm->extent.maxx = 0.0;
        cm->extent.miny = 0.0;
        cm->extent.maxy = 0.0;
        if( msOWSGetLayerExtent( layer->map, layer, "CO", &cm->extent ) == MS_FAILURE )
        return MS_FAILURE;

        /* get resolution */
        cm->xresolution = 0.0;
        cm->yresolution = 0.0;
        if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "resolution")) != NULL )
        {
            char **tokens;
            int n;

            tokens = msStringSplit(value, ' ', &n);
            if( tokens == NULL || n != 2 )
            {
                msSetError( MS_WCSERR, "Wrong number of arguments for wcs|ows_resolution metadata.", "msWCSGetCoverageMetadata()");
                msFreeCharArray( tokens, n );
                return MS_FAILURE;
            }
            cm->xresolution = atof(tokens[0]);
            cm->yresolution = atof(tokens[1]);
            msFreeCharArray( tokens, n );
        }

        /* get Size (in pixels and lines) */
        cm->xsize = 0;
        cm->ysize = 0;
        if( (value=msOWSLookupMetadata(&(layer->metadata), "COM", "size")) != NULL )
        {
            char **tokens;
            int n;

            tokens = msStringSplit(value, ' ', &n);
            if( tokens == NULL || n != 2 )
            {
                msSetError( MS_WCSERR, "Wrong number of arguments for wcs|ows_size metadata.", "msWCSGetCoverageDomain()");
                msFreeCharArray( tokens, n );
                return MS_FAILURE;
            }
            cm->xsize = atoi(tokens[0]);
            cm->ysize = atoi(tokens[1]);
            msFreeCharArray( tokens, n );
        }

        /* try to compute raster size */
        if( cm->xsize == 0 && cm->ysize == 0 && cm->xresolution != 0.0 && cm->yresolution != 0.0 && cm->extent.minx != cm->extent.maxx && cm->extent.miny != cm->extent.maxy )
        {
            cm->xsize = (int) ((cm->extent.maxx - cm->extent.minx) / cm->xresolution + 0.5);
            cm->ysize = (int) fabs((cm->extent.maxy - cm->extent.miny) / cm->yresolution + 0.5);
        }

        /* try to compute raster resolution */
        if( (cm->xresolution == 0.0 || cm->yresolution == 0.0) && cm->xsize != 0 && cm->ysize != 0 )
        {
            cm->xresolution = (cm->extent.maxx - cm->extent.minx) / cm->xsize;
            cm->yresolution = (cm->extent.maxy - cm->extent.miny) / cm->ysize;
        }

        /* do we have information to do anything */
        if( cm->xresolution == 0.0 || cm->yresolution == 0.0 || cm->xsize == 0 || cm->ysize == 0 )
        {
            msSetError( MS_WCSERR, "Failed to collect extent and resolution for WCS coverage from metadata for layer '%s'.  Need value wcs|ows_resolution or wcs|ows_size values.", "msWCSGetCoverageMetadata()", layer->name );
            return MS_FAILURE;
        }

        /* compute geotransform */
        cm->geotransform[0] = cm->extent.minx;
        cm->geotransform[1] = cm->xresolution;
        cm->geotransform[2] = 0.0;
        cm->geotransform[3] = cm->extent.maxy;
        cm->geotransform[4] = 0.0;
        cm->geotransform[5] = -fabs(cm->yresolution);

        /* get bands count, or assume 1 if not found */
        cm->numbands = 1;
        if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "bandcount")) != NULL)
        {
            cm->numbands = atoi(value);
        }

        cm->bands = msSmallCalloc(sizeof(wcs20rasterbandMetadataObj), cm->numbands);

        /* get bands type, or assume float if not found */
        cm->imagemode = MS_IMAGEMODE_FLOAT32;
        if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "imagemode")) != NULL )
        {
            if( EQUAL(value,"INT16") )
                cm->imagemode = MS_IMAGEMODE_INT16;
            else if( EQUAL(value,"FLOAT32") )
                cm->imagemode = MS_IMAGEMODE_FLOAT32;
            else if( EQUAL(value,"BYTE") )
                cm->imagemode = MS_IMAGEMODE_BYTE;
            else
            {
                msSetError( MS_WCSERR, "Content of wcs|ows_imagemode (%s) not recognised.  Should be one of PC256 (byte), INT16 or FLOAT32.", "msWCSGetCoverageMetadata()", value );
                return MS_FAILURE;
            }
        }

        if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "native_format")) != NULL )
        {
            cm->native_format = msStrdup(value);
        }

        /* determine nilvalues and reasons */
        {
            int n_nilvalues = 0, n_nilvalues_reasons = 0;
            char **t_nilvalues = NULL, **t_nilvalues_reasons = NULL;
            if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "nilvalues")) != NULL )
            {
                t_nilvalues = msStringSplit(value, ' ', &n_nilvalues);
            }
            else if((value = msOWSLookupMetadata(&(layer->metadata), "COM", "rangeset_nullvalue")) != NULL)
            {
                t_nilvalues = msStringSplit(value, ' ', &n_nilvalues);
            }

            if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", "nilvalues_reasons")) != NULL )
            {
                t_nilvalues_reasons = msStringSplit(value, ' ', &n_nilvalues_reasons);
            }

            if(n_nilvalues > 0)
            {
                int i;
                cm->numnilvalues = n_nilvalues;
                cm->nilvalues = msSmallCalloc(sizeof(char*), n_nilvalues);
                cm->nilvalues_reasons = msSmallCalloc(sizeof(char*), n_nilvalues);
                for(i = 0; i < n_nilvalues; ++i)
                {
                    cm->nilvalues[i] = msStrdup(t_nilvalues[i]);
                    if(i < n_nilvalues_reasons)
                    {
                        cm->nilvalues_reasons[i] = msStrdup(t_nilvalues_reasons[i]);
                    }
                }
            }
            msFreeCharArray(t_nilvalues, n_nilvalues);
            msFreeCharArray(t_nilvalues_reasons, n_nilvalues_reasons);
        }

        {
            char *keys[] =
                { "band_name", "band_interpretation", "band_uom", "band_definition", "band_description" };
            int nums[5], i, j;
            char **tokens[5];

            for(i = 0; i < 5; ++i)
            {
                nums[i] = 0;
                tokens[i] = NULL;
            }

            /* get string arrays from metadata for specific keys */
            for(i = 0; i < 5; ++i)
            {
                if( (value = msOWSLookupMetadata(&(layer->metadata), "COM", keys[i])) != NULL )
                {
                    tokens[i] = msStringSplit(value, ' ', &nums[i]);
                }
            }

            /* iterate over all string arrays */
            for(i = 0; i < 5; ++i)
            {
                /* if only one value for a key -> fill it to every band */
                if(nums[i] == 1)
                {
                    /* fill in every band */
                    for(j = 0; j < cm->numbands; ++j)
                    {
                        cm->bands[j].values[i] = msStrdup(tokens[i][0]);
                    }
                }
                else
                {
                    /* fill in as long as bands or values are available */
                    for(j = 0; j < nums[i] && j < cm->numbands; ++j)
                    {
                        cm->bands[j].values[i] = msStrdup(tokens[i][j]);
                    }
                }
                msFreeCharArray(tokens[i], nums[i]);
            }
        }
    }
    else if( layer->data == NULL )
    { /* no virtual metadata, not ok unless we're talking 1 image, hopefully we can fix that */
        msSetError( MS_WCSERR, "RASTER Layer with no DATA statement and no WCS virtual dataset metadata.  Tileindexed raster layers not supported for WCS without virtual dataset metadata (cm->extent, wcs_res, wcs_size).", "msWCSGetCoverageDomain()" );
        return MS_FAILURE;
    }
    else
    {   /* work from the file (e.g. DATA) */
        GDALDatasetH hDS;
        GDALDriverH hDriver;
        GDALRasterBandH hBand;
        const char szPath[MS_MAXPATHLEN];
        const char *driver_short_name, *driver_long_name;

        msGDALInitialize();

        msTryBuildPath3((char *)szPath,  layer->map->mappath, layer->map->shapepath, layer->data);
        msAcquireLock( TLOCK_GDAL );
        hDS = GDALOpen( szPath, GA_ReadOnly );
        if( hDS == NULL )
        {
            msReleaseLock( TLOCK_GDAL );
            msSetError( MS_IOERR, "%s", "msWCSGetCoverageMetadata20()", CPLGetLastErrorMsg() );
            return MS_FAILURE;
        }

        msGetGDALGeoTransform( hDS, layer->map, layer, cm->geotransform );

        cm->xsize = GDALGetRasterXSize( hDS );
        cm->ysize = GDALGetRasterYSize( hDS );

        cm->extent.minx = cm->geotransform[0];
        cm->extent.maxx = cm->geotransform[0] + cm->geotransform[1] * cm->xsize + cm->geotransform[2] * cm->ysize;
        cm->extent.miny = cm->geotransform[3] + cm->geotransform[4] * cm->xsize + cm->geotransform[5] * cm->ysize;
        cm->extent.maxy = cm->geotransform[3];

        cm->xresolution = cm->geotransform[1];
        cm->yresolution = cm->geotransform[5];

        cm->numbands = GDALGetRasterCount( hDS );

        /* TODO nilvalues? */

        if( cm->numbands == 0 )
        {
            msReleaseLock( TLOCK_GDAL );
            msSetError( MS_WCSERR, "Raster file %s has no raster bands.  This cannot be used in a layer.", "msWCSGetCoverageMetadata()", layer->data );
            return MS_FAILURE;
        }

        hBand = GDALGetRasterBand( hDS, 1 );
        switch( GDALGetRasterDataType( hBand ) )
        {
        case GDT_Byte:
            cm->imagemode = MS_IMAGEMODE_BYTE;
            break;
        case GDT_Int16:
            cm->imagemode = MS_IMAGEMODE_INT16;
            break;
        default:
            cm->imagemode = MS_IMAGEMODE_FLOAT32;
            break;
        }

        cm->bands = msSmallCalloc(sizeof(wcs20rasterbandMetadataObj), cm->numbands);

        /* get as much band metadata as possible */
        for(i = 0; i < cm->numbands; ++i)
        {
            GDALColorInterp colorInterp;
            hBand = GDALGetRasterBand(hDS, i + 1);
            colorInterp = GDALGetRasterColorInterpretation(hBand);
            cm->bands[i].name = msStrdup(GDALGetColorInterpretationName(colorInterp));
            cm->bands[i].interpretation = msStrdup(cm->bands[i].name);
            cm->bands[i].uom = msStrdup(GDALGetRasterUnitType(hBand));
            if(strlen(cm->bands[i].uom) == 0)
            {
                msFree(cm->bands[i].uom);
                cm->bands[i].uom = NULL;
            }
            /* TODO: description and definition cannot be retrieved? */
        }

        hDriver = GDALGetDatasetDriver(hDS);
        driver_short_name = GDALGetDriverShortName(hDriver);
        driver_long_name = GDALGetDriverLongName(hDriver);
        /* TODO: improve this, exchange strstr() */
        msDebug("msWCSGetCoverageMetadata20(): Driver long name = '%s' and short name = '%s'.\n", driver_long_name, driver_short_name);
        for(i = 0; i < layer->map->numoutputformats; ++i)
        {
            msDebug("msWCSGetCoverageMetadata20(): processing outputformat %s.\n", layer->map->outputformatlist[i]->driver);
            if(strstr( layer->map->outputformatlist[i]->driver, driver_short_name) != NULL
               || strstr(layer->map->outputformatlist[i]->driver, driver_long_name) != NULL)
            {
                cm->native_format = msStrdup(layer->map->outputformatlist[i]->mimetype);
                break;
            }
        }

        GDALClose( hDS );
        msReleaseLock( TLOCK_GDAL );
    }

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSClearCoverageMetadata20()                     */
/*                                                                      */
/*      Returns all dynamically allocated memory from a coverage meta-  */
/*      data object.                                                    */
/************************************************************************/

static int msWCSClearCoverageMetadata20(wcs20coverageMetadataObj *cm)
{
    int i = 0, j = 0;
    msFree(cm->native_format);
    for(i = 0; i < cm->numnilvalues; ++i)
    {
        msFree(cm->nilvalues[i]);
        msFree(cm->nilvalues_reasons[i]);
    }
    msFree(cm->nilvalues);
    msFree(cm->nilvalues_reasons);

    for(i = 0; i < cm->numbands; ++i)
    {
        for(j = 0; j < 5; ++j)
        {
            msFree(cm->bands[i].values[j]);
        }
    }
    msFree(cm->bands);
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSException20()                                 */
/*                                                                      */
/*      Writes out an OWS compliant exception.                          */
/************************************************************************/

int msWCSException20(mapObj *map, const char *exceptionCode,
                     const char *locator, const char *version)
{
    int size = 0;
    char *errorString = NULL;
    char *errorMessage = NULL;
    char *schemasLocation = NULL;
    const char * encoding;
    char *xsi_schemaLocation = NULL;
    char version_string[OWS_VERSION_MAXLEN];

    xmlDocPtr psDoc = NULL;
    xmlNodePtr psRootNode = NULL;
    xmlNodePtr psMainNode = NULL;
    xmlNodePtr psNode = NULL;
    xmlNsPtr psNsOws = NULL;
    xmlNsPtr psNsXsi = NULL;
    xmlChar *buffer = NULL;

    encoding = msOWSLookupMetadata(&(map->web.metadata), "CO", "encoding");
    errorString = msGetErrorString("\n");
    errorMessage = msEncodeHTMLEntities(errorString);
    schemasLocation = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));

    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = xmlNewNode(NULL, BAD_CAST "ExceptionReport");
    psNsOws = xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_OWS_20_NAMESPACE_URI,
                BAD_CAST MS_OWSCOMMON_OWS_NAMESPACE_PREFIX);
    xmlSetNs(psRootNode, psNsOws);

    psNsXsi = xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_PREFIX);

    /* add attributes to root element */
    xmlNewProp(psRootNode, BAD_CAST "version", BAD_CAST version);
    xmlNewProp(psRootNode, BAD_CAST "xml:lang", BAD_CAST msOWSGetLanguage(map, "exception"));

    /* get 2 digits version string: '2.0' */
    msOWSGetVersionString(OWS_2_0_0, version_string);
    version_string[3]= '\0';

    xsi_schemaLocation = msStrdup((char *)psNsOws->href);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, " ");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, (char *)schemasLocation);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, "/ows/");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, version_string);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, "/owsExceptionReport.xsd");

    /* add namespace'd attributes to root element */
    xmlNewNsProp(psRootNode, psNsXsi, BAD_CAST "schemaLocation", BAD_CAST xsi_schemaLocation);

    /* add child element */
    psMainNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Exception", NULL);

    /* add attributes to child */
    xmlNewProp(psMainNode, BAD_CAST "exceptionCode", BAD_CAST exceptionCode);

    if (locator != NULL)
    {
        xmlNewProp(psMainNode, BAD_CAST "locator", BAD_CAST locator);
    }

    if (errorMessage != NULL)
    {
        psNode = xmlNewChild(psMainNode, NULL, BAD_CAST "ExceptionText", BAD_CAST errorMessage);
    }

    /*psRootNode = msOWSCommonExceptionReport(psNsOws, OWS_2_0_0,
            schemasLocation, version, msOWSGetLanguage(map, "exception"),
            exceptionCode, locator, errorMessage);*/

    xmlDocSetRootElement(psDoc, psRootNode);

    if (encoding)
        msIO_printf("Content-type: text/xml; charset=%s%c%c", encoding, 10, 10);
    else
        msIO_printf("Content-type: text/xml%c%c", 10, 10);

    xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, (encoding ? encoding
            : "ISO-8859-1"), 1);

    msIO_printf("%s", buffer);

    //free buffer and the document
    free(errorString);
    free(errorMessage);
    free(schemasLocation);
    free(xsi_schemaLocation);
    xmlFree(buffer);
    xmlFreeDoc(psDoc);

    /* clear error since we have already reported it */
    msResetErrorList();
    return MS_FAILURE;
}

#define MAX_MIMES 20

static int msWCSGetCapabilities20_CreateProfiles(
        mapObj *map, xmlNodePtr psServiceIdentification, xmlNsPtr psOwsNs)
{
    xmlNodePtr psProfile, psTmpNode;
    char *available_mime_types[MAX_MIMES];
    int i = 0;

    /* even indices are urls, uneven are mime-types, or null*/
    char *urls_and_mime_types[] =
    {
        MS_WCS_20_PROFILE_CORE,     NULL,
        MS_WCS_20_PROFILE_KVP,      NULL,
        MS_WCS_20_PROFILE_POST,     NULL,
        MS_WCS_20_PROFILE_EPSG,     NULL,
        MS_WCS_20_PROFILE_IMAGECRS, NULL,
        MS_WCS_20_PROFILE_GEOTIFF,  "image/tiff",
        MS_WCS_20_PROFILE_GML_GEOTIFF, NULL,
        MS_WCS_20_PROFILE_SCALING, NULL,
        MS_WCS_20_PROFILE_INTERPOLATION, NULL,
        NULL, NULL /* guardian */
    };

    /* navigate to node where profiles shall be inserted */
    for(psTmpNode = psServiceIdentification->children; psTmpNode->next != NULL; psTmpNode = psTmpNode->next)
    {
        if(EQUAL((char *)psTmpNode->name, "ServiceTypeVersion"))
            break;
    }

    /* get list of all available mime types */
    msGetOutputFormatMimeList(map, available_mime_types, MAX_MIMES);

    while(urls_and_mime_types[i] != NULL)
    {
        char *mime_type;
        mime_type = urls_and_mime_types[i+1];

        /* check if there is a mime type */
        if(mime_type != NULL)
        {
            /* check if the mime_type is in the list of outputformats */
            if(CSLPartialFindString(available_mime_types, mime_type) == -1)
                continue;
        }

        /* create a new node and attach it in the tree */
        psProfile = xmlNewNode(psOwsNs, BAD_CAST "Profile");
        xmlNodeSetContent(psProfile, BAD_CAST urls_and_mime_types[i]);
        xmlAddNextSibling(psTmpNode, psProfile);

        psTmpNode = psProfile;
        i += 2;
    }
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCapabilities20_CoverageSummary()           */
/*                                                                      */
/*      Helper function to create a short summary for a specific        */
/*      coverage.                                                       */
/************************************************************************/

static int msWCSGetCapabilities20_CoverageSummary(
    mapObj *map, wcs20ParamsObjPtr params,
    xmlDocPtr doc, xmlNodePtr psContents, layerObj *layer )
{
    wcs20coverageMetadataObj cm;
    int status;
    xmlNodePtr psCSummary;

    xmlNsPtr psWcsNs = xmlSearchNs( doc, xmlDocGetRootElement(doc), BAD_CAST "wcs" );

    status = msWCSGetCoverageMetadata20(layer, &cm);
    if(status != MS_SUCCESS) return MS_FAILURE;

    psCSummary = xmlNewChild( psContents, psWcsNs, BAD_CAST "CoverageSummary", NULL );
    xmlNewChild(psCSummary, psWcsNs, BAD_CAST "CoverageId", BAD_CAST layer->name);
    xmlNewChild(psCSummary, psWcsNs, BAD_CAST "CoverageSubtype", BAD_CAST "RectifiedGridCoverage");

    msWCSClearCoverageMetadata20(&cm);

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCapabilities20()                           */
/*                                                                      */
/*      Performs the GetCapabilities operation. Writes out a xml        */
/*      structure with server specific information and a summary        */
/*      of all available coverages.                                     */
/************************************************************************/

int msWCSGetCapabilities20(mapObj *map, cgiRequestObj *req,
                           wcs20ParamsObjPtr params)
{
    xmlDocPtr psDoc = NULL;       /* document pointer */
    xmlNodePtr psRootNode, psOperationsNode, psServiceMetadataNode, psNode;
    const char *updatesequence = NULL;
    xmlNsPtr psOwsNs = NULL,
            psXLinkNs = NULL,
            psWcsNs = NULL,
            psGmlNs = NULL;
    char *script_url=NULL, *script_url_encoded=NULL;
    int i;

    /* -------------------------------------------------------------------- */
    /*      Create document.                                                */
    /* -------------------------------------------------------------------- */
    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = xmlNewNode(NULL, BAD_CAST "Capabilities");

    xmlDocSetRootElement(psDoc, psRootNode);

    /* -------------------------------------------------------------------- */
    /*      Name spaces                                                     */
    /* -------------------------------------------------------------------- */

    msWCSPrepareNamespaces20(psDoc, psRootNode, map);

    /* lookup namespaces */
    psOwsNs = xmlSearchNs( psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_OWS_NAMESPACE_PREFIX );
    psWcsNs = xmlSearchNs( psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX );
    psGmlNs = xmlSearchNs( psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_GML_NAMESPACE_PREFIX );
    psXLinkNs = xmlSearchNs( psDoc, psRootNode, BAD_CAST "xlink" );

    xmlSetNs(psRootNode, psWcsNs);

    xmlNewProp(psRootNode, BAD_CAST "version", BAD_CAST params->version );

    /* TODO: remove updatesequence? */

    updatesequence = msOWSLookupMetadata(&(map->web.metadata), "CO", "updatesequence");
    if (params->updatesequence != NULL)
    {
        i = msOWSNegotiateUpdateSequence(params->updatesequence, updatesequence);
        if (i == 0) /* current */
        {
            msSetError(MS_WCSERR, "UPDATESEQUENCE parameter (%s) is equal to server (%s)",
                    "msWCSGetCapabilities20()", params->updatesequence, updatesequence);
            return msWCSException(map, "updatesequence",
                    "CurrentUpdateSequence", params->version);
        }
        if (i > 0) /* invalid */
        {
            msSetError(MS_WCSERR, "UPDATESEQUENCE parameter (%s) is higher than server (%s)",
                    "msWCSGetCapabilities20()", params->updatesequence, updatesequence);
            return msWCSException(map, "updatesequence",
                    "InvalidUpdateSequence", params->version);
        }
    }
    if(updatesequence != NULL)
    {
        xmlNewProp(psRootNode, BAD_CAST "updateSequence", BAD_CAST updatesequence);
    }

    /* -------------------------------------------------------------------- */
    /*      Service identification.                                         */
    /* -------------------------------------------------------------------- */
    if ( MS_WCS_20_CAPABILITIES_INCLUDE_SECTION(params, "ServiceIdentification") )
    {
        psNode = xmlAddChild(psRootNode, msOWSCommonServiceIdentification(
                                    psOwsNs, map, "OGC WCS", params->version, "CO"));
        msWCSGetCapabilities20_CreateProfiles(map, psNode, psOwsNs);
    }

    /* Service Provider */
    if ( MS_WCS_20_CAPABILITIES_INCLUDE_SECTION(params, "ServiceProvider") )
    {
        xmlAddChild(psRootNode,
                msOWSCommonServiceProvider(psOwsNs, psXLinkNs, map, "CO"));
    }

    /* -------------------------------------------------------------------- */
    /*      Operations metadata.                                            */
    /* -------------------------------------------------------------------- */
    if ( MS_WCS_20_CAPABILITIES_INCLUDE_SECTION(params, "OperationsMetadata") )
    {
        if ((script_url = msOWSGetOnlineResource(map, "COM", "onlineresource", req)) == NULL
            || (script_url_encoded = msEncodeHTMLEntities(script_url)) == NULL)
        {
            msSetError(MS_WCSERR, "Server URL not found", "msWCSGetCapabilities20()");
            return msWCSException(map, "mapserv", "NoApplicableCode", params->version);
        }
        free(script_url);

        psOperationsNode = xmlAddChild(psRootNode,msOWSCommonOperationsMetadata(psOwsNs));

        /* -------------------------------------------------------------------- */
        /*      GetCapabilities - add Sections and AcceptVersions?              */
        /* -------------------------------------------------------------------- */
        psNode = msOWSCommonOperationsMetadataOperation(
            psOwsNs, psXLinkNs,
            "GetCapabilities", OWS_METHOD_GETPOST, script_url_encoded);
        xmlAddChild(psOperationsNode, psNode);

        /* -------------------------------------------------------------------- */
        /*      DescribeCoverage                                                */
        /* -------------------------------------------------------------------- */
        psNode = msOWSCommonOperationsMetadataOperation(
            psOwsNs, psXLinkNs,
            "DescribeCoverage", OWS_METHOD_GETPOST, script_url_encoded);
        xmlAddChild(psOperationsNode, psNode);

        /* -------------------------------------------------------------------- */
        /*      GetCoverage                                                     */
        /* -------------------------------------------------------------------- */
        psNode = msOWSCommonOperationsMetadataOperation(
            psOwsNs, psXLinkNs,
            "GetCoverage", OWS_METHOD_GETPOST, script_url_encoded);
        xmlAddChild(psOperationsNode, psNode);

        msFree(script_url_encoded);
    }

    /* -------------------------------------------------------------------- */
    /*      Service metadata.                                               */
    /* -------------------------------------------------------------------- */
    /* it is mandatory, but unused for now */
    psServiceMetadataNode = xmlAddChild(psRootNode, xmlNewNode(psWcsNs, BAD_CAST "ServiceMetadata"));
    xmlNewProp(psServiceMetadataNode, BAD_CAST "version", BAD_CAST "1.0.0");

    /* -------------------------------------------------------------------- */
    /*      Contents section.                                               */
    /* -------------------------------------------------------------------- */
    if ( MS_WCS_20_CAPABILITIES_INCLUDE_SECTION(params, "Contents") )
    {
        psNode = xmlNewChild( psRootNode, psWcsNs, BAD_CAST "Contents", NULL );

        for(i = 0; i < map->numlayers; ++i)
        {
            layerObj *layer = map->layers[i];
            int       status;

            if(!msWCSIsLayerSupported(layer))
                continue;

            status = msWCSGetCapabilities20_CoverageSummary(
                map, params, psDoc, psNode, layer );
            if(status != MS_SUCCESS)
            {
                xmlFreeDoc(psDoc);
                xmlCleanupParser();
                return msWCSException(map, "mapserv", "Internal", params->version);
            }
        }
    }
    /* -------------------------------------------------------------------- */
    /*      Write out the document and clean up.                            */
    /* -------------------------------------------------------------------- */
    msWCSWriteDocument20(map, psDoc);
    xmlFreeDoc(psDoc);
    xmlCleanupParser();
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSDescribeCoverage20_CoverageDescription()      */
/*                                                                      */
/*      Creates a description of a specific coverage with the three     */
/*      major sections: BoundedBy, DomainSet and RangeType.             */
/************************************************************************/

static int msWCSDescribeCoverage_CoverageDescription20(mapObj *map,
    layerObj *layer, wcs20ParamsObjPtr params, xmlDocPtr psDoc, xmlNodePtr psRootNode )
{
    int status;
    wcs20coverageMetadataObj cm;
    xmlNodePtr psCD;
    xmlNsPtr psWcsNs, psGmlNs, psGmlcovNs, psSweNs, psXLinkNs;
    psWcsNs = psGmlNs = psGmlcovNs = psSweNs = psXLinkNs = NULL;

    psWcsNs    = xmlSearchNs(psDoc, xmlDocGetRootElement(psDoc), BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX);
    psGmlNs    = xmlSearchNs(psDoc, xmlDocGetRootElement(psDoc), BAD_CAST MS_OWSCOMMON_GML_NAMESPACE_PREFIX);
    psGmlcovNs = xmlSearchNs(psDoc, xmlDocGetRootElement(psDoc), BAD_CAST MS_OWSCOMMON_GMLCOV_NAMESPACE_PREFIX);
    psSweNs    = xmlSearchNs(psDoc, xmlDocGetRootElement(psDoc), BAD_CAST MS_OWSCOMMON_SWE_NAMESPACE_PREFIX);
    psXLinkNs  = xmlSearchNs(psDoc, xmlDocGetRootElement(psDoc), BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_PREFIX);

    /* -------------------------------------------------------------------- */
    /*      Verify layer is processable.                                    */
    /* -------------------------------------------------------------------- */
    if( msCheckParentPointer(layer->map,"map") == MS_FAILURE )
        return MS_FAILURE;

    if(!msWCSIsLayerSupported(layer))
        return MS_SUCCESS;

    /* -------------------------------------------------------------------- */
    /*      Setup coverage metadata.                                        */
    /* -------------------------------------------------------------------- */
    status = msWCSGetCoverageMetadata20(layer, &cm);
    if(status != MS_SUCCESS)
        return status;

    /* fill in bands rangeset info, if required. */
    /* msWCSSetDefaultBandsRangeSetInfo( NULL, &cm, layer ); */

    /* -------------------------------------------------------------------- */
    /*      Create CoverageDescription node.                                */
    /* -------------------------------------------------------------------- */
    psCD = xmlNewChild( psRootNode, psWcsNs, BAD_CAST "CoverageDescription", NULL );
    xmlNewNsProp(psCD, psGmlNs, BAD_CAST "id", BAD_CAST layer->name);

    /* -------------------------------------------------------------------- */
    /*      gml:boundedBy                                                   */
    /* -------------------------------------------------------------------- */
    msWCSCommon20_CreateBoundedBy(layer, &cm, psGmlNs, psCD, &(layer->projection));

    xmlNewChild(psCD, psWcsNs, BAD_CAST "CoverageId", BAD_CAST layer->name);

    /* -------------------------------------------------------------------- */
    /*      gml:domainSet                                                   */
    /* -------------------------------------------------------------------- */
    msWCSCommon20_CreateDomainSet(layer, &cm, psGmlNs, psCD, &(layer->projection));

    /* -------------------------------------------------------------------- */
    /*      gmlcov:rangeType                                                */
    /* -------------------------------------------------------------------- */
    msWCSCommon20_CreateRangeType(layer, &cm, psGmlNs, psGmlcovNs, psSweNs, psXLinkNs, psCD);

    /* -------------------------------------------------------------------- */
    /*      wcs:ServiceParameters                                           */
    /* -------------------------------------------------------------------- */
    {
        xmlNodePtr psSP;

        psSP = xmlNewChild( psCD, psWcsNs, BAD_CAST "ServiceParameters", NULL);
        xmlNewChild(psSP, psWcsNs, BAD_CAST "CoverageSubtype", BAD_CAST "RectifiedGridCoverage");

        /* -------------------------------------------------------------------- */
        /*      SupportedCRS                                                    */
        /* -------------------------------------------------------------------- */

        {
            xmlNodePtr psSupportedCrss;
            char *owned_value;

            psSupportedCrss = xmlNewChild(psSP, psWcsNs,
                    BAD_CAST "SupportedCRSs", NULL);

            if ((owned_value = msOWSGetProjURI(&(layer->projection),
                    &(layer->metadata), "COM", MS_FALSE)) != NULL)
            { }
            else if ((owned_value = msOWSGetProjURI(&(layer->map->projection),
                    &(layer->map->web.metadata), "COM", MS_FALSE)) != NULL)
            { }
            else
            {
                msDebug("missing required information, no SRSs defined.\n");
            }

            if (owned_value != NULL && strlen(owned_value) > 0)
            {
                msLibXml2GenerateList(psSupportedCrss, psWcsNs,
                        "SupportedCRS", owned_value, ' ');
            }

            xmlNewChild(psSupportedCrss, psWcsNs,
                    BAD_CAST "NativeCRS", BAD_CAST cm.srs_uri);

            msFree(owned_value);
        }

        /* -------------------------------------------------------------------- */
        /*      SupportedFormats                                                */
        /* -------------------------------------------------------------------- */
        {
            xmlNodePtr psSupportedFormats;
            char *format_list;

            psSupportedFormats =
                    xmlNewChild(psSP, psWcsNs, BAD_CAST "SupportedFormats", NULL);

            format_list = msWCSGetFormatsList20(layer->map, layer);

            if (strlen(format_list) > 0)
            {
                msLibXml2GenerateList(psSupportedFormats, psWcsNs,
                        "SupportedFormat", format_list, ',');
            }

            if(cm.native_format != NULL)
            {
                xmlNewChild(psSupportedFormats, psWcsNs,
                        BAD_CAST "NativeFormat", BAD_CAST cm.native_format);
            }
            else
            {
                msDebug("msWCSDescribeCoverage20_CoverageDescription(): "
                        "No native format specified.\n");
            }

            msFree(format_list);
        }
    }

    msWCSClearCoverageMetadata20(&cm);

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSDescribeCoverage20()                          */
/*                                                                      */
/*      Implementation of the DescibeCoverage Operation. The result     */
/*      of this operation is a xml document, containing specific        */
/*      information about a coverage identified by an ID. The result    */
/*      is written on the stream.                                       */
/************************************************************************/

int msWCSDescribeCoverage20(mapObj *map, wcs20ParamsObjPtr params)
{
    xmlDocPtr psDoc = NULL; /* document pointer */
    xmlNodePtr psRootNode;
    xmlNsPtr psWcsNs = NULL;
    int i, j;

    /* create DOM document and root node */
    psDoc = xmlNewDoc(BAD_CAST "1.0");
    psRootNode = xmlNewNode(NULL, BAD_CAST "CoverageDescriptions");
    xmlDocSetRootElement(psDoc, psRootNode);

    /* prepare initial namespace definitions */
    msWCSPrepareNamespaces20(psDoc, psRootNode, map);

    psWcsNs = xmlSearchNs(psDoc, psRootNode,
            BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX);
    xmlSetNs(psRootNode, psWcsNs);

    /* check if IDs are given */
    if (params->ids)
    {
        /* for each given ID in the ID-list */
        for (j = 0; params->ids[j]; j++)
        {
            i = msGetLayerIndex(map, params->ids[j]);
            if (i == -1)
            {
                msSetError(MS_WCSERR, "Unknown coverage: (%s)",
                        "msWCSDescribeCoverage20()", params->ids[j]);
                return msWCSException(map, "NoSuchCoverage", "coverage",
                        params->version);
            }
            /* create coverage description for the specified layer */
            if(msWCSDescribeCoverage_CoverageDescription20(map, (GET_LAYER(map, i)),
                    params, psDoc, psRootNode) == MS_FAILURE)
            {
                msSetError(MS_WCSERR, "Error retrieving coverage description.", "msWCSDescribeCoverage20()");
                return msWCSException(map, "MissingParameterValue", "coverage",
                        params->version);
            }
        }
    }
    else
    {   /* Throw error, since IDs are mandatory */
        msSetError(MS_WCSERR, "Missing COVERAGEID parameter.", "msWCSDescribeCoverage20()");
        return msWCSException(map, "MissingParameterValue", "coverage",
                params->version);
    }

    /* write out the DOM document to the stream */
    msWCSWriteDocument20(map, psDoc);

    /* cleanup */
    xmlFreeDoc(psDoc);
    xmlCleanupParser();

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCoverage_FinalizeParamsObj20()             */
/*                                                                      */
/*      Finalizes a wcs20ParamsObj for a GetCoverage operation. In the  */
/*      process, the params boundig box is adjusted to the subsets,     */
/*      width, height and resolution are determined and the subset crs  */
/*      is found out.                                                   */
/************************************************************************/

static int msWCSGetCoverage20_FinalizeParamsObj(wcs20ParamsObjPtr params)
{
    int returnValue;
    static const int numAxis = 2;
    char *validXAxisNames[] = {"x", "xaxis", "x-axis", "x_axis", "long", "long_axis", "long-axis", "lon", "lon_axis", "lon-axis", NULL};
    char *validYAxisNames[] = {"y", "yaxis", "y-axis", "y_axis", "lat", "lat_axis", "lat-axis", NULL};
    char ***validAxisNames;
    char *crs = NULL;
    wcs20AxisObjPtr *axes;

    axes = (wcs20AxisObjPtr*)msSmallMalloc(sizeof(wcs20AxisObjPtr) * numAxis);

    validAxisNames = msSmallCalloc(sizeof(char**), numAxis);
    validAxisNames[0] = validXAxisNames;
    validAxisNames[1] = validYAxisNames;

    returnValue = msWCSValidateAndFindAxes20(params, validAxisNames, numAxis, axes);
    msFree(validAxisNames);
    if(returnValue != MS_SUCCESS)
    {
        msFree(axes);
        return MS_FAILURE;
    }

    if (axes[0] != NULL)
    {
        if(axes[0]->subset != NULL)
        {
            msDebug("Subset for X-axis found: %s\n", axes[0]->subset->axis);
            if (!axes[0]->subset->min.unbounded)
                params->bbox.minx = axes[0]->subset->min.scalar;
            if (!axes[0]->subset->max.unbounded)
                params->bbox.maxx = axes[0]->subset->max.scalar;
            crs = axes[0]->subset->crs;
        }
        params->width = axes[0]->size;
        params->resolutionX = axes[0]->resolution;
        if(axes[0]->resolutionUOM != NULL)
        {
            params->resolutionUnits = msStrdup(axes[0]->resolutionUOM);
        }
    }

    if (axes[1] != NULL)
    {
        if(axes[1]->subset != NULL)
        {
            msDebug("Subset for Y-axis found: %s\n", axes[1]->subset->axis);
            if (!axes[1]->subset->min.unbounded)
                params->bbox.miny = axes[1]->subset->min.scalar;
            if (!axes[1]->subset->max.unbounded)
                params->bbox.maxy = axes[1]->subset->max.scalar;
            if(crs != NULL && axes[0] != NULL && axes[0]->subset!= NULL)
            {
                if(!EQUAL(crs, axes[1]->subset->crs))
                {
                    msSetError(MS_WCSERR, "CRS for axis %s and axis %s are not the same.",
                            "msWCSCreateBoundingBox20()", axes[0]->name, axes[1]->name);
                    msFree(axes);
                    return MS_FAILURE;
                }
            }
            else
            {
                crs = axes[1]->subset->crs;
            }
        }
        params->height = axes[1]->size;
        params->resolutionY = axes[1]->resolution;

        if(params->resolutionUnits == NULL && axes[1]->resolutionUOM != NULL)
        {
            params->resolutionUnits = msStrdup(axes[1]->resolutionUOM);
        }
        else if(params->resolutionUnits != NULL && axes[1]->resolutionUOM != NULL
                && !EQUAL(params->resolutionUnits, axes[1]->resolutionUOM))
        {
            msSetError(MS_WCSERR, "The units of measure of the resolution for"
                    "axis %s and axis %s are not the same.",
                    "msWCSCreateBoundingBox20()", axes[0]->name, axes[1]->name);
            msFree(axes);
            return MS_FAILURE;
        }
    }

    msFree(axes);

    /* check if projections are equal */
    if(crs != NULL)
    {
        params->subsetcrs = msStrdup(crs);
    }
    else
    {
        params->subsetcrs = msStrdup("imageCRS");
    }

    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCoverage20_GetBands()                      */
/*                                                                      */
/*      Returns a string, containing a comma-separated list of band     */
/*      indices.                                                        */
/************************************************************************/

static int msWCSGetCoverage20_GetBands(mapObj *map, layerObj *layer,
        wcs20ParamsObjPtr params, wcs20coverageMetadataObjPtr cm, char **bandlist)
{
    int i = 0, count, maxlen, index;
    char *current = NULL, *tmp = NULL;
    char **band_ids = NULL;

    /* if rangesubset parameter is not given, default to all bands */
    if(NULL == params->range_subset)
    {
        *bandlist = msStrdup("1");
        for(i = 1; i < cm->numbands; ++i)
        {
            char strnumber[10];
            snprintf(strnumber, sizeof(strnumber), ",%d", i + 1);
            *bandlist = msStringConcatenate(*bandlist, strnumber);
        }
        return MS_SUCCESS;
    }

    count = CSLCount(params->range_subset);
    maxlen = count * 4 * sizeof(char);
    *bandlist = msSmallCalloc(sizeof(char), maxlen);
    current = *bandlist;

    tmp = msOWSGetEncodeMetadata(&layer->metadata,
                                 "COM",
                                 "rangeset_axes",
                                 NULL);
    if(NULL != tmp)
    {
        band_ids = CSLTokenizeString2(tmp, " ", 0);
        msFree(tmp);
    }

    for(i = 0; i < count; ++i)
    {
        /* print ',' if not the first value */
        if(i != 0)
        {
            current = strlcat(*bandlist, ",", maxlen) + *bandlist;
        }
        /*current += snprintf(current, maxlen - (current - *bandlist),
                                "%s%d", (i == 0) ? "" : ",", index))*/

        /* check if the string represents an integer */
        if(msStringParseInteger(params->range_subset[i], &index) == MS_SUCCESS)
        {
            tmp = msIntToString((int)index);
            strlcat(*bandlist, tmp, maxlen);
            msFree(tmp);
            /*current += snprintf(current, maxlen - (current - *bandlist),
                                "%d", index);*/
            continue;
        }

        /* check if the string is equal to a band identifier    */
        /* if so, what is the index of the band                 */
        index = CSLFindString(band_ids, params->range_subset[i]);
        if(index != -1)
        {
            tmp = msIntToString((int)index + 1);
            strlcat(*bandlist, tmp, maxlen);
            msFree(tmp);
            /*current += snprintf(current, maxlen - (current - *bandlist),
                                "%d", index+1);*/
            continue;
        }

        msSetError(MS_WCSERR, "'%s' is not a valid band identifier.",
                       "msWCSGetCoverage20_GetBands()", params->range_subset[i]);
        return MS_FAILURE;
    }
    CSLDestroy(band_ids);
    return MS_SUCCESS;
}

/************************************************************************/
/*                   msWCSGetCoverage20()                               */
/*                                                                      */
/*      Implementation of the GetCoverage Operation. The coverage       */
/*      is either returned as an image or as a multipart xml/image.     */
/*      The result is written on the stream.                            */
/************************************************************************/

int msWCSGetCoverage20(mapObj *map, cgiRequestObj *request,
                       wcs20ParamsObjPtr params)
{
    layerObj *layer = NULL;
    wcs20coverageMetadataObj cm;
    imageObj *image = NULL;
    outputFormatObj *format = NULL;

    rectObj subsets, bbox;
    projectionObj imageProj;

    int status, i;
    double x_1, x_2, y_1, y_2;
    char *coverageName, *bandlist=NULL, numbands[8];

    /* number of coverage ids should be 1 */
    if (params->ids == NULL || params->ids[0] == NULL) {
        msSetError(MS_WCSERR, "Required parameter CoverageID was not supplied.",
                   "msWCSGetCoverage20()");
        return msWCSException(map, "MissingParameterValue", "coverage",
                              params->version);
    }
    if (params->ids[1] != NULL) {
        msSetError(MS_WCSERR, "GetCoverage operation supports only one coverage.",
                   "msWCSGetCoverage20()");
        return msWCSException(map, "TooManyParameterValues", "coverage",
                              params->version);
    }

    /* find the right layer */
    layer = NULL;
    for(i = 0; i < map->numlayers; i++) {
        coverageName = msOWSGetEncodeMetadata(&(GET_LAYER(map, i)->metadata),
                                              "COM", "name",
                                              GET_LAYER(map, i)->name);
        if (EQUAL(coverageName, params->ids[0]))
        {
            layer = GET_LAYER(map, i);
            i = map->numlayers; /* to exit loop don't use break, we want to free resources first */
        }
        msFree(coverageName);
    }

    /* throw exception if no Layer was found */
    if (layer == NULL)
    {
        msSetError(MS_WCSERR,
                "COVERAGE=%s not found, not in supported layer list.",
                "msWCSGetCoverage20()", params->ids[0]);
        return msWCSException(map, "InvalidParameterValue", "coverage",
                params->version);
    }
    /* retrieve coverage metadata  */
    status = msWCSGetCoverageMetadata20(layer, &cm);
    if (status != MS_SUCCESS) return MS_FAILURE;

    /* fill in bands rangeset info, if required.  */
    //msWCSSetDefaultBandsRangeSetInfo(NULL, &cm, layer );

    /* set  resolution, size and maximum extent */
    layer->extent = map->extent = cm.extent;
    map->cellsize = cm.xresolution;
    map->width = cm.xsize;
    map->height = cm.ysize;

    /************************************************************************/
    /*      finalize the params object. determine subset crs and subset     */
    /*      bbox. Also project the image to the subset crs.                 */
    /************************************************************************/

    msInitProjection(&imageProj);
    msLoadProjectionString(&imageProj, cm.srs);

    if(msWCSGetCoverage20_FinalizeParamsObj(params) == MS_FAILURE)
    {
        return msWCSException(map, "InvalidParameterValue", "extent", params->version);
    }

    subsets = params->bbox;

    if(EQUAL(params->subsetcrs, "imageCRS"))
    {
        /* subsets are in imageCRS; reproject them to real coordinates */
        rectObj orig_bbox = subsets;

        msFreeProjection(&(map->projection));
        map->projection = imageProj;

        if(subsets.minx != -DBL_MAX || subsets.maxx != DBL_MAX)
        {
            x_1 = cm.geotransform[0]
                + orig_bbox.minx * cm.geotransform[1]
                + orig_bbox.miny * cm.geotransform[2];
            x_2 =
                    cm.geotransform[0]
                + (orig_bbox.maxx+1) * cm.geotransform[1]
                + (orig_bbox.maxy+1) * cm.geotransform[2];

            subsets.minx = MIN(x_1, x_2);
            subsets.maxx = MAX(x_1, x_2);
        }
        if(subsets.miny != -DBL_MAX || subsets.maxy != DBL_MAX)
        {
            y_1 = cm.geotransform[3]
                + (orig_bbox.maxx+1) * cm.geotransform[4]
                + (orig_bbox.maxy+1) * cm.geotransform[5];
            /*subsets.miny -= cm.geotransform[4]/2 + cm.geotransform[5]/2;*/
            y_2 = cm.geotransform[3]
                + orig_bbox.minx * cm.geotransform[4]
                + orig_bbox.miny * cm.geotransform[5];

            subsets.miny = MIN(y_1, y_2);
            subsets.maxy = MAX(y_1, y_2);
        }
    }
    else /* if crs is not the 'imageCRS' */
    {
        projectionObj subsetProj;

        /* if the subsets have a crs given, project the image extent to it */
        msInitProjection(&subsetProj);
        if(msLoadProjectionString(&subsetProj, params->subsetcrs) != MS_SUCCESS)
        {
            msSetError(MS_WCSERR,
                "Error loading CRS %s.",
                "msWCSGetCoverage20()", params->subsetcrs);
            return MS_FAILURE;
        }

        if(msProjectionsDiffer(&imageProj, &subsetProj))
        {
            msProjectRect(&imageProj, &subsetProj, &(layer->extent));
            map->extent = layer->extent;
            msFreeProjection(&(map->projection));
            map->projection = subsetProj;
        }
        else
        {
            map->projection = imageProj;
        }
    }

    /* create boundings of params subsets and image extent */
    if(msRectOverlap(&subsets, &(layer->extent)) == MS_FALSE)
    {
        /* extent and bbox do not overlap -> exit */
        msSetError(MS_WCSERR, "Image extent does not intersect with desired region.",
                "msWCSGetCoverage20()");
        return msWCSException(map, "ExtentError", "extent", params->version);
    }

    /* write combined bounding box */
    bbox.minx = MAX(subsets.minx, map->extent.minx);
    bbox.miny = MAX(subsets.miny, map->extent.miny);
    bbox.maxx = MIN(subsets.maxx, map->extent.maxx);
    bbox.maxy = MIN(subsets.maxy, map->extent.maxy);

    /* check if we are overspecified  */
    if((params->width != 0 &&  params->resolutionX != MS_WCS20_UNBOUNDED)
            || (params->height != 0 && params->resolutionY != MS_WCS20_UNBOUNDED))
    {
        msSetError(MS_WCSERR, "GetCoverage operation supports only one of SIZE or RESOLUTION per axis.",
               "msWCSGetCoverage20()");
        return msWCSException(map, "TooManyParameterValues", "coverage",
                          params->version);
    }

    /************************************************************************/
    /* check both axes: see if either size or resolution are given (and     */
    /* calculate the other value). If both are not given, calculate them    */
    /* from the bounding box.                                               */
    /************************************************************************/

    /* check x axis */
    if(params->width != 0)
    {
        /* TODO Unit Of Measure? */
        params->resolutionX = (bbox.maxx - bbox.minx) / params->width;
    }
    else if(params->resolutionX != MS_WCS20_UNBOUNDED)
    {
        params->width = MS_NINT((bbox.maxx - bbox.minx) / params->resolutionX);
    }
    else
    {
        if(ABS(bbox.maxx - bbox.minx) != ABS(map->extent.maxx - map->extent.minx))
        {
            double total = ABS(map->extent.maxx - map->extent.minx),
                    part = ABS(bbox.maxx - bbox.minx);
            params->width = MS_NINT((part * map->width) / total);
        }
        else
        {
            params->width = map->width;
        }

        params->resolutionX = (bbox.maxx - bbox.minx) / params->width;
    }

    /* check y axis */
    if(params->height != 0)
    {
        params->resolutionY = (bbox.maxy - bbox.miny) / params->height;
    }
    else if(params->resolutionY != MS_WCS20_UNBOUNDED)
    {
        params->height = MS_NINT((bbox.maxy - bbox.miny) / params->resolutionY);
    }
    else
    {
        if(ABS(bbox.maxy - bbox.miny) != ABS(map->extent.maxy - map->extent.miny))
        {
            double total = ABS(map->extent.maxy - map->extent.miny),
                    part = ABS(bbox.maxy - bbox.miny);
            params->height = MS_NINT((part * map->height) / total);
        }
        else
        {
            params->height = map->height;
        }

        params->resolutionY = (bbox.maxy - bbox.miny) / params->height;
    }

    /* WCS 2.0 is center of pixel oriented */
    bbox.minx += params->resolutionX * 0.5;
    bbox.maxx -= params->resolutionX * 0.5;
    bbox.miny += params->resolutionY * 0.5;
    bbox.maxy -= params->resolutionY * 0.5;

    /* if parameter 'outputcrs' is given, project the image to this crs */
    if(params->outputcrs != NULL)
    {
        projectionObj outputProj;

        msInitProjection(&outputProj);
        if(msLoadProjectionString(&outputProj, params->outputcrs) == -1)
        {
            msFreeProjection(&outputProj);
            return msWCSException(map, "InvalidParameterValue", "coverage",
                  params->version);
        }
        if(msProjectionsDiffer(&(map->projection), &outputProj))
        {

            msDebug("msWCSGetCoverage20(): projecting to outputcrs %s\n", params->outputcrs);

            msProjectRect(&(map->projection), &outputProj, &bbox);
            msFreeProjection(&(map->projection));
            map->projection = outputProj;
        }
    }

    /* set the bounding box as new map extent */
    map->extent = layer->extent = bbox;
    map->width = params->width;
    map->height = params->height;

    /* Mapserver only supports square cells */
    if (params->resolutionX <= params->resolutionY)
        map->cellsize = params->resolutionX;
    else
        map->cellsize = params->resolutionY;

    msDebug("msWCSGetCoverage20(): Set parameters from original"
                   "data. Width: %d, height: %d, cellsize: %f, extent: %f,%f,%f,%f\n",
               map->width, map->height, map->cellsize, map->extent.minx,
               map->extent.miny, map->extent.maxx, map->extent.maxy);

    if (!params->format)
    {
        msSetError(MS_WCSERR, "Required parameter FORMAT was not supplied.",
                "msWCSGetCoverage20()");
        return msWCSException(map, "MissingParameterValue", "format",
                params->version);
    }

    /*    make sure layer is on   */
    layer->status = MS_ON;

    msMapComputeGeotransform(map);

    /*    fill in bands rangeset info, if required.  */
    //msWCSSetDefaultBandsRangeSetInfo(params, &cm, layer);
    //msDebug("Bandcount: %d\n", cm.bandcount);

    if (msGetOutputFormatIndex(map, params->format) == -1)
    {
        msSetError(MS_WCSERR, "Unrecognized value for the FORMAT parameter.",
                "msWCSGetCoverage20()");
        return msWCSException(map, "InvalidParameterValue", "format",
                params->version);
    }

    /* create a temporary outputformat (we likely will need to tweak parts) */
    format = msCloneOutputFormat(msSelectOutputFormat(map, params->format));
    msApplyOutputFormat(&(map->outputformat), format, MS_NOOVERRIDE,
            MS_NOOVERRIDE, MS_NOOVERRIDE);

    if(msWCSGetCoverage20_GetBands(map, layer, params, &cm, &bandlist) != MS_SUCCESS)
    {
        return msWCSException(map, "InvalidParameterValue", "format",
                params->version);
    }
    msLayerSetProcessingKey(layer, "BANDS", bandlist);
    snprintf(numbands, sizeof(numbands), "%d", msCountChars(bandlist, ',')+1);
    msSetOutputFormatOption(map->outputformat, "BAND_COUNT", numbands);
    msFree(bandlist);

    /* check for the interpolation */
    /* Defaults to NEAREST */
    if(params->interpolation != NULL)
    {
        if(EQUALN(params->interpolation,"NEAREST",7))
        {
            msLayerSetProcessingKey(layer, "RESAMPLE", "NEAREST");
        }
        else if(EQUAL(params->interpolation,"BILINEAR"))
        {
            msLayerSetProcessingKey(layer, "RESAMPLE", "BILINEAR");
        }
        else if(EQUAL(params->interpolation,"AVERAGE"))
        {
            msLayerSetProcessingKey(layer, "RESAMPLE", "AVERAGE");
        }
        else
        {
            msSetError( MS_WCSERR, "'%s' specifies an unsupported interpolation method.",
                    "msWCSGetCoverage20()", params->interpolation );
            return msWCSException(map, "InvalidParameterValue", "interpolation", params->version);
        }
    } else { 
        msLayerSetProcessingKey(layer, "RESAMPLE", "NEAREST");
    }

    /* since the dataset is only used in one layer, set it to be    */
    /* closed after drawing the layer. This normally defaults to    */
    /* DEFER and will produce a memory leak, because the dataset    */
    /* will not be closed.                                          */
    if( msLayerGetProcessingKey(layer, "CLOSE_CONNECTION") == NULL )
    {
        msLayerSetProcessingKey(layer, "CLOSE_CONNECTION", "NORMAL");
    }

    /* create the image object  */
    if (!map->outputformat)
    {
        msSetError(MS_WCSERR, "The map outputformat is missing!",
                "msWCSGetCoverage20()");
        return msWCSException(map, NULL, NULL, params->version);
    }
    else if (MS_RENDERER_PLUGIN(map->outputformat))
    {
        image = msImageCreate(map->width, map->height, map->outputformat,
                map->web.imagepath, map->web.imageurl, map->resolution,
                map->defresolution, &map->imagecolor); 
    } 
    else if (MS_RENDERER_RAWDATA(map->outputformat)) 
    { 
        image = msImageCreate(map->width, map->height, map->outputformat,
                map->web.imagepath, map->web.imageurl, map->resolution,
                map->defresolution, &map->imagecolor);
    }
    else
    {
        msSetError(MS_WCSERR, "Map outputformat not supported for WCS!",
                "msWCSGetCoverage20()");
        return msWCSException(map, NULL, NULL, params->version);
    }

    if (image == NULL)
        return msWCSException(map, NULL, NULL, params->version);

    /* Actually produce the "grid". */
    status = msDrawRasterLayerLow( map, layer, image, NULL );
    if( status != MS_SUCCESS ) {
        return msWCSException(map, NULL, NULL, params->version );
    }
    msDebug("image:%s\n", image->imagepath);


    /* GML+GeoTIFF */
    /* Embed the GeoTIFF into multipart message */
    if(params->multipart == MS_TRUE)
    {
        xmlDocPtr psDoc = NULL;       /* document pointer */
        xmlNodePtr psRootNode, psRangeSet, psFile, psRangeParameters;
        xmlNsPtr psGmlNs = NULL,
            psGmlcovNs = NULL,
            psSweNs = NULL,
            psWcsNs = NULL,
            psXLinkNs = NULL;
        wcs20coverageMetadataObj tmpCm;
        char *srs_uri, *filename, *default_filename;
        char *file_ref;
        int length = 0;

        /* Create Document  */
        psDoc = xmlNewDoc(BAD_CAST "1.0");
        psRootNode = xmlNewNode(NULL, BAD_CAST MS_WCS_GML_COVERAGETYPE_RECTIFIED_GRID_COVERAGE);
        xmlDocSetRootElement(psDoc, psRootNode);

        msWCSPrepareNamespaces20(psDoc, psRootNode, map);

        psGmlNs    = xmlSearchNs(psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_GML_NAMESPACE_PREFIX);
        psGmlcovNs = xmlSearchNs(psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_GMLCOV_NAMESPACE_PREFIX);
        psSweNs    = xmlSearchNs(psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_SWE_NAMESPACE_PREFIX);
        psWcsNs    = xmlSearchNs(psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_WCS_NAMESPACE_PREFIX);
        psXLinkNs  = xmlSearchNs(psDoc, psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_PREFIX);

        xmlNewNsProp(psRootNode, psGmlNs, BAD_CAST "id", BAD_CAST layer->name);

        xmlSetNs(psRootNode, psGmlcovNs);

        srs_uri = msOWSGetProjURI(&map->projection, NULL, "COM", 1);

        tmpCm = cm;
        tmpCm.extent = map->extent;
        tmpCm.xsize = params->width;
        tmpCm.ysize = params->height;
        tmpCm.xresolution = params->resolutionX;
        tmpCm.yresolution = params->resolutionY;
        strlcpy(tmpCm.srs_uri, srs_uri, sizeof(tmpCm.srs_uri));
        msFree(srs_uri);
        /* WCS 2.0 is center of pixel oriented */
        tmpCm.extent.minx -= params->resolutionX * 0.5;
        tmpCm.extent.maxx += params->resolutionX * 0.5;
        tmpCm.extent.miny -= params->resolutionY * 0.5;
        tmpCm.extent.maxy += params->resolutionY * 0.5;


        /* Setup layer information  */
        msWCSCommon20_CreateBoundedBy(layer, &tmpCm, psGmlNs, psRootNode, &(map->projection));
        msWCSCommon20_CreateDomainSet(layer, &tmpCm, psGmlNs, psRootNode, &(map->projection));

        psRangeSet = xmlNewChild(psRootNode, psGmlNs, BAD_CAST "rangeSet", NULL);
        psFile     = xmlNewChild(psRangeSet, psGmlNs, BAD_CAST "File", NULL);

        /* TODO: wait for updated specifications */
        psRangeParameters = xmlNewChild(psFile, psGmlNs, BAD_CAST "rangeParameters", NULL);

        default_filename = msStrdup("out.");
        default_filename = msStringConcatenate(default_filename, MS_IMAGE_EXTENSION(image->format));

        filename = msGetOutputFormatOption(image->format, "FILENAME", default_filename);
        length = strlen("coverage/") + strlen(filename) + 1;
        file_ref = msSmallMalloc(length);
        strlcpy(file_ref, "coverage/", length);
        strlcat(file_ref, filename, length);

        msDebug("File reference: %s\n", file_ref);

        xmlNewNsProp(psRangeParameters, psXLinkNs, BAD_CAST "href", BAD_CAST file_ref);
        xmlNewNsProp(psRangeParameters, psXLinkNs, BAD_CAST "role", BAD_CAST MS_IMAGE_MIME_TYPE(map->outputformat));
        xmlNewNsProp(psRangeParameters, psXLinkNs, BAD_CAST "arcrole", BAD_CAST "fileReference");

        xmlNewChild(psFile, psGmlNs, BAD_CAST "fileReference", BAD_CAST file_ref);
        xmlNewChild(psFile, psGmlNs, BAD_CAST "fileStructure", NULL);
        xmlNewChild(psFile, psGmlNs, BAD_CAST "mimeType", BAD_CAST MS_IMAGE_MIME_TYPE(map->outputformat));

        msWCSCommon20_CreateRangeType(layer, &cm, psGmlNs, psGmlcovNs, psSweNs, psXLinkNs, psRootNode);

        msIO_printf( "Content-Type: multipart/mixed; boundary=wcs%c%c"
                     "--wcs\n", 10, 10);

        msWCSWriteDocument20(map, psDoc);
        msWCSWriteFile20(map, image, params, 1);
        xmlFreeDoc(psDoc);
        xmlCleanupParser();
    }
    /* just print out the file without gml */
    else
    {
        msWCSWriteFile20(map, image, params, 0);
    }

    msWCSClearCoverageMetadata20(&cm);
    msFreeImage(image);
    return MS_SUCCESS;
}

#endif /* defined(USE_LIBXML2) */

/************************************************************************/
/*                   msWCSDispatch20()                                  */
/*                                                                      */
/*      Dispatches a mapserver request. First the cgiRequest is         */
/*      parsed. Afterwards version and service are beeing checked.      */
/*      If they aren't compliant, MS_DONE is returned. Otherwise        */
/*      either GetCapabilities, DescribeCoverage or GetCoverage         */
/*      operations are executed.                                        */
/************************************************************************/

int msWCSDispatch20(mapObj *map, cgiRequestObj *request)
{
    wcs20ParamsObjPtr params = NULL;
    int returnValue = MS_FAILURE, status;

    params = msWCSCreateParamsObj20();
    status = msWCSParseRequest20(request, params);

#if defined(USE_LIBXML2)
    if(status == MS_FAILURE)
    {
        msDebug("msWCSDispatch20(): Parse error occurred.\n");
        msWCSException20(map, "InvalidParameterValue", "request", "2.0.0" );
        msWCSFreeParamsObj20(params);
        return MS_FAILURE;
    }
    else if(status == MS_DONE)
    {
        /* could not be parsed, but no error */
        /* continue for now...               */
    }

    /* first check if Service is WCS */
    if (params->service == NULL
        && !EQUAL(params->service, "WCS"))
    {
        /* The service is not WCS, exit with MS_DONE */
        msDebug("msWCSDispatch20(): wrong service (%s)\n",
                (params->service != NULL) ? params->service : "none");
        msWCSFreeParamsObj20(params);
        msResetErrorList();
        return MS_DONE;
    }

    /* check if request is set */
    if(params->request == NULL)
    {
        /* If service is WCS, a request must be set. */
        /* Therefore, exit with a failure.           */
        msSetError(MS_WCSERR, "Missing REQUEST parameter",
                "msWCSDispatch20()");
        msWCSException20(map, "MissingParameterValue", "request",
                params->version );
        msWCSFreeParamsObj20(params); /* clean up */
        return MS_FAILURE;
    }

    /* Handle version negotiation for GetCapabilities. */
    /* Only if accepted versions are given, and not a  */
    /* predefined version.                             */
    if (EQUAL(params->request, "GetCapabilities")
        && params->accept_versions != NULL
        && params->version         == NULL)
    {
        int i, highest_version = 0;
        char version_string[OWS_VERSION_MAXLEN];
        for(i = 0; params->accept_versions[i] != NULL; ++i)
        {
            int version = msOWSParseVersionString(params->accept_versions[i]);
            if (version == OWS_VERSION_BADFORMAT)
            {
                msWCSException20(map, "InvalidParameterValue",
                        "request", "2.0.0" );
                msWCSFreeParamsObj20(params);
                return MS_FAILURE;
            }
            if(version > highest_version)
            {
                highest_version = version;
            }
        }
        msOWSGetVersionString(highest_version, version_string);
        params->version = msStrdup(version_string);
    }

    /* Now the version has to be set */
    if(params->version == NULL
        || !EQUAL(params->version, "2.0.0"))
    {
        msDebug("msWCSDispatch20(): version and service are not compliant with WCS 2.0.0\n");
        msWCSFreeParamsObj20(params);
        msResetErrorList();
        return MS_DONE;
    }

    /* check if any unknown parameters are present              */
    /* create an error message, containing all unknown params   */
    if (params->invalid_get_parameters != NULL)
    {
        char *concat = NULL;
        int i, count = CSLCount(params->invalid_get_parameters);
        for(i = 0; i < count; ++i)
        {
            concat = msStringConcatenate(concat, (char *)"'");
            concat = msStringConcatenate(concat, params->invalid_get_parameters[i]);
            concat = msStringConcatenate(concat, (char *)"'");
            if(i + 1 != count)
            {
                concat = msStringConcatenate(concat, ", ");
            }
        }
        msSetError(MS_WCSERR, "Unknown parameter%s: %s.",
                "msWCSParseRequest20()", (count > 1) ? "s" : "", concat);
        msFree(concat);
        msWCSFreeParamsObj20(params);
        return msWCSException(map, "InvalidParameterValue", "request", "2.0.0");
    }

    /* check if all layer names are valid NCNames */
    {
        int i;
        for(i = 0; i < map->numlayers; ++i)
        {
            if(!msWCSIsLayerSupported(map->layers[i]))
                continue;

            if(msStringIsNCName(map->layers[i]->name) == MS_FALSE)
            {
                msSetError(MS_WCSERR, "Layer name '%s' is not a valid NCName.",
                        "msWCSDescribeCoverage20()", map->layers[i]->name);
                msWCSFreeParamsObj20(params);
                return msWCSException(map, "mapserv", "Internal", "2.0.0");
            }
        }
    }

    /* Call operation specific functions */
    if (EQUAL(params->request, "GetCapabilities"))
    {
        returnValue = msWCSGetCapabilities20(map, request, params);
    }
    else if (EQUAL(params->request, "DescribeCoverage"))
    {
        returnValue = msWCSDescribeCoverage20(map, params);
    }
    else if (EQUAL(params->request, "GetCoverage"))
    {
        returnValue = msWCSGetCoverage20(map, request, params);
    }
    else
    {
        msSetError(MS_WCSERR, "Invalid request '%s'.",
                "msWCSDispatch20()", params->request);
        returnValue = msWCSException20(map, "InvalidParameterValue",
                "request", params->version);
    }
    /* clean up */
    msWCSFreeParamsObj20(params);
    return returnValue;

#else /* defined(USE_LIBXML2) */
    if(params->service && params->version &&
            EQUAL(params->service, "WCS") && EQUAL(params->version, "2.0.0", 3))
    {
        msSetError(MS_WCSERR, "WCS 2.0.0 needs mapserver to be compiled with libxml2.", "msWCSDispatch20()");
        return msWCSException(map, "mapserv", "NoApplicableCode", "1.0.0");
    }
    else
    {
        return MS_DONE;
    }
#endif /* defined(USE_LIBXML2) */
}

#endif /* defined(USE_WCS_SVR) */
