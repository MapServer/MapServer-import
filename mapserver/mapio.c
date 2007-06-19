/******************************************************************************
 *
 * Project:  MapServer
 * Purpose:  Implementations for MapServer IO redirection capability.
 * Author:   Frank Warmerdam, warmerdam@pobox.com
 *
 ******************************************************************************
 * Copyright (c) 2004, Frank Warmerdam <warmerdam@pobox.com>
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
 ****************************************************************************/

#include <stdarg.h>

#include "map.h"
#include "mapthread.h"

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

MS_CVSID("$Id$")

static int is_msIO_initialized = MS_FALSE;

typedef struct msIOContextGroup_t
{
    msIOContext stdin_context;
    msIOContext stdout_context;
    msIOContext stderr_context;

    int    thread_id;
    struct msIOContextGroup_t *next;
} msIOContextGroup;

static msIOContextGroup default_contexts;
static msIOContextGroup *io_context_list = NULL;
static void msIO_Initialize( void );

#ifdef msIO_printf
#  undef msIO_printf
#  undef msIO_fprintf
#  undef msIO_fwrite
#  undef msIO_fread
#  undef msIO_vfprintf
#endif

/************************************************************************/
/*                            msIO_Cleanup()                            */
/************************************************************************/

void msIO_Cleanup()

{
    if( is_msIO_initialized )

    {
        is_msIO_initialized = MS_FALSE;
        while( io_context_list != NULL )
        {
            msIOContextGroup *last = io_context_list;
            io_context_list = io_context_list->next;
            free( last );
        }
    }
}

/************************************************************************/
/*                        msIO_GetContextGroup()                        */
/************************************************************************/

static msIOContextGroup *msIO_GetContextGroup()

{
    int nThreadId = msGetThreadId();
    msIOContextGroup *prev = NULL, *group = io_context_list;

    if( group != NULL && group->thread_id == nThreadId )
        return group;

/* -------------------------------------------------------------------- */
/*      Search for group for this thread                                */
/* -------------------------------------------------------------------- */
    msAcquireLock( TLOCK_IOCONTEXT );
    msIO_Initialize();

    group = io_context_list;
    while( group != NULL && group->thread_id != nThreadId )
    {
        prev = group;
        group = group->next;
    }

/* -------------------------------------------------------------------- */
/*      If we found it, make sure it is pushed to the front of the      */
/*      link for faster finding next time, and return it.               */
/* -------------------------------------------------------------------- */
    if( group != NULL )
    {
        if( prev != NULL )
        {
            prev->next = group->next;
            group->next = io_context_list;
            io_context_list = group;
        }

        msReleaseLock( TLOCK_IOCONTEXT );
        return group;
    }

/* -------------------------------------------------------------------- */
/*      Create a new context group for this thread.                     */
/* -------------------------------------------------------------------- */
    group = (msIOContextGroup *) calloc(sizeof(msIOContextGroup),1);
    
    group->stdin_context = default_contexts.stdin_context;
    group->stdout_context = default_contexts.stdout_context;
    group->stderr_context = default_contexts.stderr_context;
    group->thread_id = nThreadId;

    group->next = io_context_list;
    io_context_list = group;
    
    msReleaseLock( TLOCK_IOCONTEXT );

    return group;
}

/************************************************************************/
/*                          msIO_getHandler()                           */
/************************************************************************/

msIOContext *msIO_getHandler( FILE * fp )

{
    int nThreadId = msGetThreadId();
    msIOContextGroup *group = io_context_list;

    msIO_Initialize();

    if( group == NULL || group->thread_id != nThreadId )
    {
        group = msIO_GetContextGroup();
        if( group == NULL )
            return NULL;
    }

    if( fp == stdin || fp == NULL || strcmp((const char *)fp,"stdin") == 0 )
        return &(group->stdin_context);
    else if( fp == stdout || strcmp((const char *)fp,"stdout") == 0 )
        return &(group->stdout_context);
    else if( fp == stderr || strcmp((const char *)fp,"stderr") == 0 )
        return &(group->stderr_context);
    else
        return NULL;
}

/************************************************************************/
/*                        msIO_installHandlers()                        */
/************************************************************************/

int msIO_installHandlers( msIOContext *stdin_context,
                          msIOContext *stdout_context,
                          msIOContext *stderr_context )

{
    msIOContextGroup *group;

    msIO_Initialize();

    group = msIO_GetContextGroup();
    
    if( stdin_context == NULL )
        group->stdin_context = default_contexts.stdin_context;
    else if( stdin_context != &group->stdin_context )
        group->stdin_context = *stdin_context;
    
    if( stdout_context == NULL )
        group->stdout_context = default_contexts.stdout_context;
    else if( stdout_context != &group->stdout_context )
        group->stdout_context = *stdout_context;
    
    if( stderr_context == NULL )
        group->stderr_context = default_contexts.stderr_context;
    else if( stderr_context != &group->stderr_context )
        group->stderr_context = *stderr_context;
    
    return MS_TRUE;
}

/************************************************************************/
/*                          msIO_contextRead()                          */
/************************************************************************/

int msIO_contextRead( msIOContext *context, void *data, int byteCount )

{
    if( context->write_channel == MS_TRUE )
        return 0;
    else
        return context->readWriteFunc( context->cbData, data, byteCount );
}

/************************************************************************/
/*                         msIO_contextWrite()                          */
/************************************************************************/

int msIO_contextWrite( msIOContext *context, const void *data, int byteCount )

{
    if( context->write_channel == MS_FALSE )
        return 0;
    else
        return context->readWriteFunc( context->cbData, (void *) data, 
                                       byteCount );
}

/* ==================================================================== */
/* ==================================================================== */
/*      Stdio-like cover functions.                                     */
/* ==================================================================== */
/* ==================================================================== */

/************************************************************************/
/*                            msIO_printf()                             */
/************************************************************************/

int msIO_printf( const char *format, ... )

{
    va_list args;
    int     return_val;
    msIOContext *context;
    char workBuf[8000];

    va_start( args, format );
#if defined(HAVE_VSNPRINTF)
    return_val = vsnprintf( workBuf, sizeof(workBuf), format, args );
#else
    return_val = vsprintf( workBuf, format, args);
#endif

    va_end( args );

    if( return_val < 0 || return_val >= sizeof(workBuf) )
        return -1;

    context = msIO_getHandler( stdout );
    if( context == NULL )
        return -1;

    return msIO_contextWrite( context, workBuf, return_val );
}

/************************************************************************/
/*                            msIO_fprintf()                            */
/************************************************************************/

int msIO_fprintf( FILE *fp, const char *format, ... )

{
    va_list args;
    int     return_val;
    msIOContext *context;
    char workBuf[8000];

    va_start( args, format );
#if defined(HAVE_VSNPRINTF)
    return_val = vsnprintf( workBuf, sizeof(workBuf), format, args );
#else
    return_val = vsprintf( workBuf, format, args);
#endif

    va_end( args );

    if( return_val < 0 || return_val >= sizeof(workBuf) )
        return -1;

    context = msIO_getHandler( fp );
    if( context == NULL )
        return fwrite( workBuf, 1, return_val, fp );
    else
        return msIO_contextWrite( context, workBuf, return_val );
}

/************************************************************************/
/*                            msIO_vfprintf()                           */
/************************************************************************/

int msIO_vfprintf( FILE *fp, const char *format, va_list ap )

{
    int     return_val;
    msIOContext *context;
    char workBuf[8000];

#if defined(HAVE_VSNPRINTF)
    return_val = vsnprintf( workBuf, sizeof(workBuf), format, ap );
#else
    return_val = vsprintf( workBuf, format, ap );
#endif

    if( return_val < 0 || return_val >= sizeof(workBuf) )
        return -1;

    context = msIO_getHandler( fp );
    if( context == NULL )
        return fwrite( workBuf, 1, return_val, fp );
    else
        return msIO_contextWrite( context, workBuf, return_val );
}

/************************************************************************/
/*                            msIO_fwrite()                             */
/************************************************************************/

int msIO_fwrite( const void *data, size_t size, size_t nmemb, FILE *fp )

{
    msIOContext *context;

    context = msIO_getHandler( fp );
    if( context == NULL )
        return fwrite( data, size, nmemb, fp );
    else
        return msIO_contextWrite( context, data, size * nmemb ) / size;
}

/************************************************************************/
/*                            msIO_fread()                              */
/************************************************************************/

int msIO_fread( void *data, size_t size, size_t nmemb, FILE *fp )

{
    msIOContext *context;

    context = msIO_getHandler( fp );
    if( context == NULL )
        return fread( data, size, nmemb, fp );
    else
        return msIO_contextRead( context, data, size * nmemb ) / size;
}

/* ==================================================================== */
/* ==================================================================== */
/*      Internal default callbacks implementing stdio reading and       */
/*      writing.                                                        */
/* ==================================================================== */
/* ==================================================================== */

/************************************************************************/
/*                           msIO_stdioRead()                           */
/*                                                                      */
/*      This is the default implementation via stdio.                   */
/************************************************************************/

static int msIO_stdioRead( void *cbData, void *data, int byteCount )

{
    return fread( data, 1, byteCount, (FILE *) cbData );
}

/************************************************************************/
/*                          msIO_stdioWrite()                           */
/*                                                                      */
/*      This is the default implementation via stdio.                   */
/************************************************************************/

static int msIO_stdioWrite( void *cbData, void *data, int byteCount )

{
    return fwrite( data, 1, byteCount, (FILE *) cbData );
}

/************************************************************************/
/*                          msIO_Initialize()                           */
/************************************************************************/

static void msIO_Initialize( void )

{
    if( is_msIO_initialized == MS_TRUE )
        return;

    default_contexts.stdin_context.label = "stdio";
    default_contexts.stdin_context.write_channel = MS_FALSE;
    default_contexts.stdin_context.readWriteFunc = msIO_stdioRead;
    default_contexts.stdin_context.cbData = (void *) stdin;

    default_contexts.stdout_context.label = "stdio";
    default_contexts.stdout_context.write_channel = MS_TRUE;
    default_contexts.stdout_context.readWriteFunc = msIO_stdioWrite;
    default_contexts.stdout_context.cbData = (void *) stdout;

    default_contexts.stderr_context.label = "stdio";
    default_contexts.stderr_context.write_channel = MS_TRUE;
    default_contexts.stderr_context.readWriteFunc = msIO_stdioWrite;
    default_contexts.stderr_context.cbData = (void *) stderr;

    default_contexts.next = NULL;
    default_contexts.thread_id = 0;

    is_msIO_initialized = MS_TRUE;
}

/* ==================================================================== */
/* ==================================================================== */
/*      Stuff related to having a gdIOCtx operate through the msIO      */
/*      layer.                                                          */
/* ==================================================================== */
/* ==================================================================== */

typedef struct {
    gdIOCtx        gd_io_ctx;
    msIOContext    *ms_io_ctx;
} msIO_gdIOCtx;

/************************************************************************/
/*                            msIO_gd_putC()                            */
/*                                                                      */
/*      A GD IO context callback to put a character, redirected         */
/*      through the msIO output context.                                */
/************************************************************************/

static void msIO_gd_putC( gdIOCtx *cbData, int out_char )

{
    msIO_gdIOCtx *merged_context = (msIO_gdIOCtx *) cbData;
    char out_char_as_char = (char) out_char;

    msIO_contextWrite( merged_context->ms_io_ctx, &out_char_as_char, 1 );
}

/************************************************************************/
/*                           msIO_gd_putBuf()                           */
/*                                                                      */
/*      The GD IO context callback to put a buffer of data,             */
/*      redirected through the msIO output context.                     */
/************************************************************************/

static int msIO_gd_putBuf( gdIOCtx *cbData, const void *data, int byteCount )

{
    msIO_gdIOCtx *merged_context = (msIO_gdIOCtx *) cbData;

    return msIO_contextWrite( merged_context->ms_io_ctx, data, byteCount );
}

/************************************************************************/
/*                          msIO_getGDIOCtx()                           */
/*                                                                      */
/*      The returned context should be freed with free() when no        */
/*      longer needed.                                                  */
/************************************************************************/

gdIOCtx *msIO_getGDIOCtx( FILE *fp )

{
    msIO_gdIOCtx *merged_context;
    msIOContext *context = msIO_getHandler( fp );

    if( context == NULL )
        return NULL;

    merged_context = (msIO_gdIOCtx *) calloc(1,sizeof(msIO_gdIOCtx));
    merged_context->gd_io_ctx.putC = msIO_gd_putC;
    merged_context->gd_io_ctx.putBuf = msIO_gd_putBuf;
    merged_context->ms_io_ctx = context;

    return (gdIOCtx *) merged_context;
}

/* ==================================================================== */
/* ==================================================================== */
/*      FastCGI output redirection functions.                           */
/* ==================================================================== */
/* ==================================================================== */

#ifdef USE_FASTCGI

#define NO_FCGI_DEFINES
#include "fcgi_stdio.h"

/************************************************************************/
/*                           msIO_fcgiRead()                            */
/*                                                                      */
/*      This is the default implementation via stdio.                   */
/************************************************************************/

static int msIO_fcgiRead( void *cbData, void *data, int byteCount )

{
    return FCGI_fread( data, 1, byteCount, (FCGI_FILE *) cbData );
}

/************************************************************************/
/*                           msIO_fcgiWrite()                           */
/*                                                                      */
/*      This is the default implementation via stdio.                   */
/************************************************************************/

static int msIO_fcgiWrite( void *cbData, void *data, int byteCount )

{
    return FCGI_fwrite( data, 1, byteCount, (FCGI_FILE *) cbData );
}

/************************************************************************/
/*                    msIO_installFastCGIRedirect()                     */
/************************************************************************/

int msIO_installFastCGIRedirect()

{
    msIOContext stdin_ctx, stdout_ctx, stderr_ctx;

    stdin_ctx.label = "fcgi";
    stdin_ctx.write_channel = MS_FALSE;
    stdin_ctx.readWriteFunc = msIO_fcgiRead;
    stdin_ctx.cbData = (void *) FCGI_stdin;

    stdout_ctx.label = "fcgi";
    stdout_ctx.write_channel = MS_TRUE;
    stdout_ctx.readWriteFunc = msIO_fcgiWrite;
    stdout_ctx.cbData = (void *) FCGI_stdout;

    stderr_ctx.label = "fcgi";
    stderr_ctx.write_channel = MS_TRUE;
    stderr_ctx.readWriteFunc = msIO_fcgiWrite;
    stderr_ctx.cbData = (void *) FCGI_stderr;

    msIO_installHandlers( &stdin_ctx, &stdout_ctx, &stderr_ctx );

    return MS_TRUE;
}

#endif

/************************************************************************/
/*                       msIO_needBinaryStdout()                        */
/*                                                                      */
/*      This function is intended to ensure that stdout is in binary    */
/*      mode.                                                           */
/*                                                                      */
/*      But don't do it we are using FastCGI.  We will take care of     */
/*      doing it in the libfcgi library in that case for the normal     */
/*      cgi case, and for the fastcgi case the _setmode() call          */
/*      causes a crash.                                                 */
/************************************************************************/

int msIO_needBinaryStdout()

{
#if defined(_WIN32) && !defined(USE_FASTCGI)
    if(_setmode( _fileno(stdout), _O_BINARY) == -1) 
    {
      msSetError(MS_IOERR, 
                 "Unable to change stdout to binary mode.", 
                 "msIO_needBinaryStdout()" );
      return(MS_FAILURE);
    }
#endif
    
    return MS_SUCCESS;
}

/************************************************************************/
/*                        msIO_needBinaryStdin()                        */
/*                                                                      */
/*      This function is intended to ensure that stdin is in binary     */
/*      mode.                                                           */
/*                                                                      */
/*      But don't do it we are using FastCGI.  We will take care of     */
/*      doing it in the libfcgi library in that case for the normal     */
/*      cgi case, and for the fastcgi case the _setmode() call          */
/*      causes a crash.                                                 */
/************************************************************************/

int msIO_needBinaryStdin()

{
#if defined(_WIN32) && !defined(USE_FASTCGI)
    if(_setmode( _fileno(stdin), _O_BINARY) == -1) 
    {
      msSetError(MS_IOERR, 
                 "Unable to change stdin to binary mode.", 
                 "msIO_needBinaryStdin()" );
      return(MS_FAILURE);
    }
#endif
    
    return MS_SUCCESS;
}

/* ==================================================================== */
/*      memory buffer io handling functions.                            */
/* ==================================================================== */

/************************************************************************/
/*                         msIO_resetHandlers()                         */
/************************************************************************/

void msIO_resetHandlers()

{
    msIOContextGroup *group = msIO_GetContextGroup();

    if( group == NULL )
        return;

    if( strcmp(group->stdin_context.label,"buffer") == 0 )
    {
        msIOBuffer *buf = (msIOBuffer *) group->stdin_context.cbData;
        
        if( buf->data != NULL )
            free( buf->data );
        free( buf );
    }

    if( strcmp(group->stdout_context.label,"buffer") == 0 )
    {
        msIOBuffer *buf = (msIOBuffer *) group->stdout_context.cbData;
        
        if( buf->data != NULL )
            free( buf->data );
        free( buf );
    }

    if( strcmp(group->stderr_context.label,"buffer") == 0 )
    {
        msIOBuffer *buf = (msIOBuffer *) group->stderr_context.cbData;
        
        if( buf->data != NULL )
            free( buf->data );
        free( buf );
    }

    msIO_installHandlers( NULL, NULL, NULL );
}

/************************************************************************/
/*                     msIO_installStdoutToBuffer()                     */
/************************************************************************/

void msIO_installStdoutToBuffer()

{
    msIOContextGroup *group = msIO_GetContextGroup();
    msIOContext  context;
    
    context.label = "buffer";
    context.write_channel = MS_TRUE;
    context.readWriteFunc = msIO_bufferWrite;
    context.cbData = calloc(sizeof(msIOBuffer),1);

    msIO_installHandlers( &group->stdin_context, 
                          &context, 
                          &group->stderr_context );
}

/************************************************************************/
/*                    msIO_installStdinFromBuffer()                     */
/************************************************************************/

void msIO_installStdinFromBuffer()

{
    msIOContextGroup *group = msIO_GetContextGroup();
    msIOContext  context;

    context.label = "buffer";
    context.write_channel = MS_FALSE;
    context.readWriteFunc = msIO_bufferRead;
    context.cbData = calloc(sizeof(msIOBuffer),1);

    msIO_installHandlers( &context, 
                          &group->stdout_context, 
                          &group->stderr_context );
}

/************************************************************************/
/*                 msIO_stripStdoutBufferContentType()                  */
/*                                                                      */
/*      Strip off content-type header from buffer, and return to        */
/*      caller.  Returned string is the callers responsibility to       */
/*      call msFree() on to deallocate.  This function will return      */
/*      NULL if there is no content-type header.                        */
/************************************************************************/

char *msIO_stripStdoutBufferContentType()

{
/* -------------------------------------------------------------------- */
/*      Find stdout buffer.                                             */
/* -------------------------------------------------------------------- */
    msIOContext *ctx = msIO_getHandler( (FILE *) "stdout" );
    msIOBuffer  *buf;
    char *content_type = NULL;
    int end_of_ct, start_of_data;

    if( ctx == NULL || ctx->write_channel == MS_FALSE 
        || strcmp(ctx->label,"buffer") != 0 )
    {
	msSetError( MS_MISCERR, "Can't identify msIO buffer.",
                    "msIO_stripStdoutBufferContentType" );
	return NULL;
    }

    buf = (msIOBuffer *) ctx->cbData;

/* -------------------------------------------------------------------- */
/*      Return NULL if we don't have a content-type header.             */
/* -------------------------------------------------------------------- */
    if( buf->data_offset < 14 
        || strncasecmp((const char*) buf->data,"Content-type: ",14) != 0 )
        return NULL;

/* -------------------------------------------------------------------- */
/*      Find newline marker at end of content type argument.            */
/* -------------------------------------------------------------------- */
    end_of_ct = 13;
    while( end_of_ct+1 < buf->data_offset 
           && buf->data[end_of_ct+1] != 10 )
        end_of_ct++;

    if( end_of_ct+1 == buf->data_offset )
    {
	msSetError( MS_MISCERR, "Corrupt Content-type header.",
                    "msIO_stripStdoutBufferContentType" );
	return NULL;
    }

/* -------------------------------------------------------------------- */
/*      Continue on to the start of data ... skipping two newline       */
/*      markers.                                                        */
/* -------------------------------------------------------------------- */
    start_of_data = end_of_ct+2;
    while( start_of_data  < buf->data_offset 
           && buf->data[start_of_data] != 10 )
        start_of_data++;

    if( start_of_data == buf->data_offset )
    {
	msSetError( MS_MISCERR, "Corrupt Content-type header.",
                    "msIO_stripStdoutBufferContentType" );
	return NULL;
    }

    start_of_data++;

/* -------------------------------------------------------------------- */
/*      Copy out content type.                                          */
/* -------------------------------------------------------------------- */
    content_type = (char *) malloc(end_of_ct-14+2);
    strncpy( content_type, (const char *) buf->data + 14, end_of_ct - 14 + 1);
    content_type[end_of_ct-14+1] = '\0';

/* -------------------------------------------------------------------- */
/*      Move data to front of buffer, and reset length.                 */
/* -------------------------------------------------------------------- */
    memmove( buf->data, buf->data+start_of_data, 
             buf->data_offset - start_of_data );
    buf->data[buf->data_offset - start_of_data] = '\0';
    buf->data_offset -= start_of_data;

    return content_type;
}

/************************************************************************/
/*                          msIO_bufferWrite()                          */
/************************************************************************/

int msIO_bufferWrite( void *cbData, void *data, int byteCount )

{
    msIOBuffer *buf = (msIOBuffer *) cbData;

    /*
    ** Grow buffer if needed.
    */
    if( buf->data_offset + byteCount > buf->data_len )
    {
        buf->data_len = buf->data_len * 2 + byteCount + 100;
        if( buf->data == NULL )
            buf->data = (unsigned char *) malloc(buf->data_len);
        else
            buf->data = (unsigned char *) realloc(buf->data, buf->data_len);

        if( buf->data == NULL )
        {
            msSetError( MS_MEMERR, 
                        "Failed to allocate %d bytes for capture buffer.",
                        "msIO_bufferWrite()", buf->data_len );
            buf->data_len = 0;
            return 0;
        }
    }

    /*
    ** Copy result into buffer.
    */

    memcpy( buf->data + buf->data_offset, data, byteCount );
    buf->data_offset += byteCount;

    return byteCount;
}

/************************************************************************/
/*                          msIO_bufferRead()                           */
/************************************************************************/

int msIO_bufferRead( void *cbData, void *data, int byteCount )

{
/*    msIOBuffer *buf = (msIOBuffer *) cbData; */

    /* not implemented yet. */

    return 0;
}
