/**********************************************************************
 * $Id$
 *
 * Name:     php_mapscript_util.h
 * Project:  PHP/MapScript extension for MapServer : Utility functions
 * Language: ANSI C
 * Purpose:  Utility functions
 * Author:   Daniel Morissette, morissette@dmsolutions.ca
 *
 **********************************************************************
 * Copyright (c) 2000, 2001, Daniel Morissette, DM Solutions Group
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
 *
 * $Log$
 * Revision 1.5  2002/03/07 22:31:01  assefa
 * Add template processing functions.
 *
 * Revision 1.4  2001/09/13 20:56:27  dan
 * Added _phpms_fetch_property_resource().
 *
 * Revision 1.3  2001/01/09 05:24:41  dan
 * Fixes to build with PHP 4.0.4
 *
 * Revision 1.2  2000/09/08 21:27:54  dan
 * Added _phpms_object_init()
 *
 * Revision 1.1  2000/09/06 19:44:07  dan
 * Ported module to PHP4
 *
 *
 */

#ifdef PHP4
#include "php.h"
#include "php_globals.h"
#else
#include "phpdl.h"
#include "php3_list.h"
#endif

/**********************************************************************
 *                  macros for setting object properties
 **********************************************************************/
#define IF_SET_LONG(php_name, internal_var)                     \
  if (strcmp(pPropertyName->value.str.val, php_name) == 0)      \
  {                                                             \
    convert_to_long(pNewValue);                                 \
    _phpms_set_property_long(pThis,php_name, pNewValue->value.lval, E_ERROR); \
    internal_var = pNewValue->value.lval;                       \
  }

#define IF_SET_DOUBLE(php_name, internal_var)                   \
  if (strcmp(pPropertyName->value.str.val, php_name) == 0)      \
  {                                                             \
    _phpms_set_property_double(pThis,php_name,pNewValue->value.dval,E_ERROR); \
    internal_var = pNewValue->value.dval;                       \
  }

#define IF_SET_STRING(php_name, internal_var)                   \
  if (strcmp(pPropertyName->value.str.val, php_name) == 0)      \
  {                                                             \
    _phpms_set_property_string(pThis,php_name,pNewValue->value.str.val,E_ERROR); \
    if (internal_var) free(internal_var);                       \
    internal_var = NULL;                                        \
    if (pNewValue->value.str.val)                               \
      internal_var = strdup(pNewValue->value.str.val);          \
  }

#define IF_SET_BYTE(php_name, internal_var)                     \
  if (strcmp(pPropertyName->value.str.val, php_name) == 0)      \
  {                                                             \
    convert_to_long(pNewValue);                                 \
    _phpms_set_property_long(pThis,php_name, pNewValue->value.lval, E_ERROR); \
    internal_var = (unsigned char)pNewValue->value.lval;                       \
  }

#define PHPMS_ADD_PROP_STR(ret_val, name, value) \
  add_property_string(ret_val, name, (value)?(value):"", 1)


/* -------------------------------------------------------------------- */
/*      _phpms_object_init() and PHP4_CLASS_ENTRY() provide a common    */
/*      method to create PHP3/PHP4 obects.                              */
/* -------------------------------------------------------------------- */
int _phpms_object_init(pval *return_value, int  handle_id,
                       function_entry *class_functions,
                       void           *zend_class_entry_ptr );
#ifdef PHP4
#  define PHP4_CLASS_ENTRY(a) a
#else
#  define PHP4_CLASS_ENTRY(a) NULL
#endif


/* -------------------------------------------------------------------- */
/*      prototypes                                                      */
/* -------------------------------------------------------------------- */
void _phpms_report_mapserver_error(int php_err_type);

void *_phpms_fetch_handle2(pval *pObj, 
                           int handle_type1, int handle_type2, 
                           HashTable *list);

void *_phpms_fetch_handle(pval *pObj, int handle_type, 
                          HashTable *list);

char *_phpms_fetch_property_handle2(pval *pObj, char *property_name, 
                                    int handle_type1, int handle_type2,
                                    HashTable *list, int err_type);
char *_phpms_fetch_property_handle(pval *pObj, char *property_name, 
                                   int handle_type, HashTable *list,
                                   int err_type);
char *_phpms_fetch_property_string(pval *pObj, char *property_name, 
                                   int err_type);
long _phpms_fetch_property_long(pval *pObj, char *property_name, 
                                int err_type);
double _phpms_fetch_property_double(pval *pObj, char *property_name,
                                    int err_type);
long _phpms_fetch_property_resource(pval *pObj, char *property_name, 
                                    int err_type);
int _phpms_set_property_string(pval *pObj, char *property_name, 
                               char *szNewValue, int err_type);
int _phpms_set_property_long(pval *pObj, char *property_name, 
                             long lNewValue, int err_type);
int _phpms_set_property_double(pval *pObj, char *property_name, 
                               double dNewValue, int err_type);
int _phpms_add_property_object(pval *pObj,      
                               char *property_name, pval *pObjToAdd,
                               int err_type);
int _php_extract_associative_array(HashTable *php, char **array);


