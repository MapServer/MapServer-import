/* $Id$ */

#include "map.h"

#include <ctype.h>

#ifdef NEED_STRLCAT
/*
 * Copyright (c) 1998 Todd C. Miller <Todd.Miller@courtesan.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

/*
 * Appends src to string dst of size siz (unlike strncat, siz is the
 * full size of dst, not space left).  At most siz-1 characters
 * will be copied.  Always NUL terminates (unless siz <= strlen(dst)).
 * Returns strlen(src) + MIN(siz, strlen(initial dst)).
 * If retval >= siz, truncation occurred.
 */
size_t strlcat(char *dst, const char *src, size_t siz)
{
  register char *d = dst;
  register const char *s = src;
  register size_t n = siz;
  size_t dlen;

  /* Find the end of dst and adjust bytes left but don't go past end */
  while (n-- != 0 && *d != '\0')
    d++;
  dlen = d - dst;
  n = siz - dlen;

  if (n == 0)
    return(dlen + strlen(s));
  while (*s != '\0') {
    if (n != 1) {
      *d++ = *s;
      n--;
    }
    s++;
  }
  *d = '\0';

  return(dlen + (s - src));/* count does not include NUL */
}
#endif

#ifdef NEED_STRDUP
char	*strdup(char *s)
{
  char	*s1;

  if(!s)
    return(NULL);
  s1 = (char *)malloc(strlen(s) + 1);
  if(!s1)
    return(NULL);

  strcpy(s1,s);
  return(s1);
}
#endif

#ifdef NEED_STRNCASECMP
int strncasecmp(const char *s1, const char *s2, int len)
{
  register const char *cp1, *cp2;
  int cmp = 0;

  cp1 = s1;
  cp2 = s2;
  
  while(*cp1 && *cp2 && len) 
  {
      if((cmp = (toupper(*cp1) - toupper(*cp2))) != 0)
        return(cmp);
      cp1++;
      cp2++;
      len--;
  }
  
  if(len == 0) {
    return(0);
  }
  if(*cp1 || *cp2)
  {
      if (*cp1)
        return(1);
      else
        return (-1);
  }
  return(0);
}
#endif

#ifdef NEED_STRCASECMP
int strcasecmp(const char *s1, const char *s2)
{
  register const char *cp1, *cp2;
  int cmp = 0;

  cp1 = s1;
  cp2 = s2;
  while(*cp1 && *cp2) 
  {
     if((cmp = (toupper(*cp1) - toupper(*cp2))) != 0)
        return(cmp);
    cp1++;
    cp2++;
  }
  if(*cp1 || *cp2)
  {
      if (*cp1)
        return(1);
      else
        return (-1);
  }

  return(0);
}
#endif

char *long2string(long value) {
  static char buffer[256]; // plenty of space

  sprintf(buffer, "%ld", value);
  return(strdup(buffer));
}

char *double2string(double value) {
  static char buffer[256]; // plenty of space

  sprintf(buffer, "%g", value);
  return(strdup(buffer));
}

char *chop(char *string) {  
  int n;

  n = strlen(string);
  if(n>0)
    string[n-1] = '\0';

  return(string);
}

/* ------------------------------------------------------------------------------- */
/*       Trims leading blanks from a string                                        */
/* ------------------------------------------------------------------------------- */
void trimBlanks(char *string)
{
   int i,n;

   n = strlen(string);
   for(i=n-1;i>=0;i--) { /* step backwards through the string */
      if(string[i] != ' ') { 
	string[i+1] = '\0'; 
	return; 
      }
   }
}

/* ------------------------------------------------------------------------------- */
/*       Trims end-of-line marker from a string                                    */
/*       Usefull in conjunction with fgets() calls                                 */
/* ------------------------------------------------------------------------------- */
void trimEOL(char *string)
{
  int i;

  for(i=0;i<strlen(string);i++) {
    if(string[i] == '\n') {
      string[i] = '\0'; /* Terminate the string at the newline */
      return;
    }
  }
}

/* ------------------------------------------------------------------------------- */
/*       Replace all occurances of old with new in str.                            */
/*       It is assumed that str was dynamically created using malloc.              */
/* ------------------------------------------------------------------------------- */
char *gsub(char *str, const char *old, const char *new)
{
      size_t str_len, old_len, new_len, tmp_offset;
      char *tmp_ptr;

      if(new == NULL)
          new = "";

      /*
      ** If old is not found then leave str alone
      */
      if( (tmp_ptr = strstr(str, old)) == NULL)
	return(str);

      /*
      ** Grab some info about incoming strings
      */
      str_len = strlen(str);
      old_len = strlen(old);
      new_len = strlen(new);

      /*
      ** Now loop until old is NOT found in new
      */
      while( tmp_ptr != NULL ) {

	/*
	** re-allocate memory for buf assuming 1 replacement of old with new
        ** don't bother reallocating if old is larger than new)
	*/
        if (old_len < new_len) {
          tmp_offset = tmp_ptr - str;
          str_len = str_len - old_len + new_len;
          str = (char *)realloc(str, (str_len + 1)); /* make new space for a copy */
          tmp_ptr = str + tmp_offset;
        }

        /*
        ** Move the trailing part of str to make some room unless old_len == new_len
        */
        if (old_len != new_len) {
            memmove(tmp_ptr+new_len, tmp_ptr+old_len, strlen(tmp_ptr)-old_len+1);
        }

        /*
        ** Now copy new over old
        */
        memcpy(tmp_ptr, new, new_len);

        /*
        ** And look for more matches in the rest of the string
        */
        tmp_ptr = strstr(tmp_ptr + new_len, old);
      }

      return(str);
}

/*
** how many times does ch occur in str
*/
int countChars(char *str, char ch) 
{
  int i, l, n=0;

  l = strlen(str);
  for(i=0;i<l;i++)
    if(str[i] == ch) n++;

  return(n);
}

/* ------------------------------------------------------------------------------- */
/*       Strip filename from a full path                                           */
/* ------------------------------------------------------------------------------- */
char *stripPath(char *fn)
{
  char *str;

  if((str = strrchr(fn,'/')) != NULL) { /* return pointer to last "slash" */
    str++; /* skip past the "slash" */
    return(str);
  } else
    return(fn);
}

/*
** Returns the *path* portion of the filename fn. Memory is allocated using malloc.
*/
char *getPath(char *fn)
{
  char *str;
  int i, length;
  
  length = strlen(fn);
  if((str = strdup(fn)) == NULL)
    return(NULL);
  
  for(i=length-1; i>=0; i--) { /* step backwards through the string */
    if((str[i] == '/') || (str[i] == '\\')) { 
      str[i+1] = '\0'; 
      break;
    }
  }

#if defined(_WIN32) && !defined(__CYGWIN__)  
  if(strcmp(str, fn) == 0)
    strcpy(str, ".\\");
#else
  if(strcmp(str, fn) == 0)
    strcpy(str, "./");
#endif  

  return(str);
}

/*
** Returns a *path* built from abs_path and path.
** The pszReturnPath must be declared by the caller function as an array
** of MS_MAXPATHLEN char
*/
char *msBuildPath(char *pszReturnPath, const char *abs_path, const char *path)
{
  int   abslen = 0;
  int   pathlen = 0;


  if(path == NULL)
  {
      msSetError(MS_IOERR, NULL, "msBuildPath");
      return NULL;
  }

  pathlen = strlen(path);
  if (abs_path)
    abslen = strlen(abs_path);

  if((pathlen + abslen + 2) > MS_MAXPATHLEN)
  {
      msSetError(MS_IOERR, "(%s%s): path is too long", "msBuildPath()",
                 abs_path, path);
      return NULL;
  }

  // Check if path is absolute
  if((abs_path == NULL) || (abslen == 0) || 
       (path[0] == '\\') || (path[0] == '/') || 
         (pathlen > 1 && (path[1] == ':')))
  {
      strcpy(pszReturnPath, path);
      return(pszReturnPath);
  }

  // else return abs_path/path
  if((abs_path[abslen-1] == '/') || (abs_path[abslen-1] == '\\'))
  {
      sprintf(pszReturnPath, "%s%s", abs_path, path);
  }
  else
  {
      sprintf(pszReturnPath, "%s/%s", abs_path, path);
  }

  return(pszReturnPath);
}

/*
** Returns a *path* built from abs_path, path1 and path2.
** abs_path/path1/path2
** The pszReturnPath must be declared by the caller function as an array
** of MS_MAXPATHLEN char
*/
char *msBuildPath3(char *pszReturnPath, const char *abs_path, const char *path1,const char *path2)
{
  char szPath[MS_MAXPATHLEN];

  return msBuildPath(pszReturnPath, abs_path, 
                     msBuildPath(szPath, path1, path2));
}

/*
** Similar to msBuildPath(), but the input path is only qualified by the
** absolute path if this will result in it pointing to a readable file.
**
** Returns NULL if the resulting path doesn't point to a readable file.
*/

char *msTryBuildPath(char *szReturnPath, const char *abs_path, const char *path)

{
    FILE	*fp;

    if( msBuildPath( szReturnPath, abs_path, path ) == NULL )
        return NULL;

    fp = fopen( szReturnPath, "r" );
    if( fp == NULL )
    {
        strcpy( szReturnPath, path );
        return NULL;
    }
    else
        fclose( fp );

    return szReturnPath;
}

/*
** Similar to msBuildPath3(), but the input path is only qualified by the
** absolute path if this will result in it pointing to a readable file.
**
** Returns NULL if the resulting path doesn't point to a readable file.
*/

char *msTryBuildPath3(char *szReturnPath, const char *abs_path, const char *path1, const char *path2)

{
    FILE	*fp;

    if( msBuildPath3( szReturnPath, abs_path, path1, path2 ) == NULL )
        return NULL;

    fp = fopen( szReturnPath, "r" );
    if( fp == NULL )
    {
        strcpy( szReturnPath, path2 );
        return NULL;
    }
    else
        fclose( fp );

    return szReturnPath;
}

/*
** Splits a string into multiple strings based on ch. Consecutive ch's are ignored.
*/
char **split(const char *string, char ch, int *num_tokens) 
{
  int i,j,k;
  int length,n;
  char **token;
  char last_ch='\0';

  n = 1; /* always at least 1 token, the string itself */
  length = strlen(string);
  for(i=0; i<length; i++) {
    if(string[i] == ch && last_ch != ch)
      n++;
    last_ch = string[i];
  }

  token = (char **) malloc(sizeof(char *)*n);
  if(!token) return(NULL);
  
  k = 0;
  token[k] = (char *)malloc(sizeof(char)*(length+1));
  if(!token[k]) return(NULL);

  j = 0;
  last_ch='\0';
  for(i=0; i<length; i++) {
    if(string[i] == ch) {
      
      if(last_ch == ch)
	continue;
      
      token[k][j] = '\0'; /* terminate current token */      
      
      k++;
      token[k] = (char *)malloc(sizeof(char)*(length+1));
      if(!token[k]) return(NULL);
      
      j = 0;      
    } else {      
      token[k][j] = string[i];
      j++;
    }
    
    last_ch = string[i]; 
  }

  token[k][j] = '\0'; /* terminate last token */

  *num_tokens = n;

  return(token);
}

char *msEncodeUrl(const char *data)
{
  char *hex = "0123456789ABCDEF";
  const char *i;
  char  *j, *code;
  int   inc;
  unsigned char ch;

  for (inc=0, i=data; *i!='\0'; i++)
    if (!isalnum(*i))
      inc += 2;
  
  if (!(code = (char*)malloc(strlen(data)+inc+1)))
    return NULL;
  
  for (j=code, i=data; *i!='\0'; i++, j++)
    {
      if (*i == ' ')
	*j = '+';
      else
      if (!isalnum(*i))
	{
	  ch = *i;
	  *j++ = '%';
	  *j++ = hex[ch/16];
	  *j   = hex[ch%16];
	}
      else
	*j = *i;
    }
  *j = '\0';
  
  return code;
}

/* msEncodeHTMLEntities()
**
** Return a copy of string after replacing some problematic chars with their
** HTML entity equivalents.
**
** The replacements performed are:
**  '&' -> "&amp;", '"' -> "&quot;", '<' -> "&lt;" and '>' -> "&gt;"
**/
char *msEncodeHTMLEntities(const char *string) 
{
    int buflen, i;
    char *newstring;
    const char *c;

    // Start with 100 extra chars for replacements... 
    // should be good enough for most cases
    buflen = strlen(string) + 100;
    newstring = (char*)malloc(buflen+1*sizeof(char*));
    if (newstring == NULL)
    {
        msSetError(MS_MEMERR, NULL, "msEncodeHTMLEntities()");
        return NULL;
    }

    for(i=0, c=string; *c != '\0'; c++)
    {
        // Need to realloc buffer?
        if (i+6 > buflen)
        {
            // If we had to realloc then this string must contain several
            // entities... so let's go with twice the previous buffer size
            buflen *= 2;
            newstring = (char*)realloc(newstring, buflen+1*sizeof(char*));
            if (newstring == NULL)
            {
                msSetError(MS_MEMERR, NULL, "msEncodeHTMLEntities()");
                return NULL;
            }
        }

        switch(*c)
        {
          case '&':
            strcpy(newstring+i, "&amp;");
            i += 5;
            break;
          case '<':
            strcpy(newstring+i, "&lt;");
            i += 4;
            break;
          case '>':
            strcpy(newstring+i, "&gt;");
            i += 4;
            break;
          case '"':
            strcpy(newstring+i, "&quot;");
            i += 6;
            break;
          case '\'':
            strcpy(newstring+i, "&apos;");
            i += 6;
            break;
          default:
            newstring[i++] = *c;
        }
    }

    newstring[i++] = '\0';

    return newstring;
}


/* msDecodeHTMLEntities()
**
** Modify the string to replace encoded characters by their true value
**
** The replacements performed are:
**  "&amp;" -> '&', "&quot;" -> '"', "&lt;" -> '<' and "&gt;" -> '>'
**/
void msDecodeHTMLEntities(const char *string) 
{
    char *pszAmp=NULL, *pszSemiColon=NULL, *pszReplace=NULL, *pszEnd=NULL;
    char *pszBuffer=NULL;

    if(string == NULL)
        return;
    else
        pszBuffer = (char*)string;

    pszReplace = (char*) malloc(sizeof(char) * strlen(pszBuffer));
    pszEnd = (char*) malloc(sizeof(char) * strlen(pszBuffer));

    while((pszAmp = strchr(pszBuffer, '&')) != NULL)
    {
        // Get the &...;
        strcpy(pszReplace, pszAmp);
        pszSemiColon = strchr(pszReplace, ';');
        if(pszSemiColon == NULL)
            break;
        else
            pszSemiColon++;

        // Get everything after the &...;
        strcpy(pszEnd, pszSemiColon);

        pszReplace[pszSemiColon-pszReplace] = '\0';

        // Replace the &...;
        if(strcasecmp(pszReplace, "&amp;") == 0)
        {
            pszBuffer[pszAmp - pszBuffer] = '&';
            pszBuffer[pszAmp - pszBuffer + 1] = '\0';
            strcat(pszBuffer, pszEnd);
        }
        else if(strcasecmp(pszReplace, "&lt;") == 0)
        {
            pszBuffer[pszAmp - pszBuffer] = '<';
            pszBuffer[pszAmp - pszBuffer + 1] = '\0';
            strcat(pszBuffer, pszEnd);
        }
        else if(strcasecmp(pszReplace, "&gt;") == 0)
        {
            pszBuffer[pszAmp - pszBuffer] = '>';
            pszBuffer[pszAmp - pszBuffer + 1] = '\0';
            strcat(pszBuffer, pszEnd);
        }
        else if(strcasecmp(pszReplace, "&quot;") == 0)
        {
            pszBuffer[pszAmp - pszBuffer] = '"';
            pszBuffer[pszAmp - pszBuffer + 1] = '\0';
            strcat(pszBuffer, pszEnd);
        }
        else if(strcasecmp(pszReplace, "&apos;") == 0)
        {
            pszBuffer[pszAmp - pszBuffer] = '\'';
            pszBuffer[pszAmp - pszBuffer + 1] = '\0';
            strcat(pszBuffer, pszEnd);
        }

        pszBuffer = pszAmp + 1;
    }

    free(pszReplace);
    free(pszEnd);

    return;
}

/*
 * Concatenate pszSrc to pszDest and reallocate memory if necessary.
*/
char *strcatalloc(char *pszDest, char *pszSrc)
{
   int nLen;
   
   if (pszSrc == NULL)
      return pszDest;

   // if destination is null, allocate memory
   if (pszDest == NULL) {
      pszDest = strdup(pszSrc);
   }
   else { // if dest is not null, reallocate memory
      char *pszTemp;

      nLen = strlen(pszDest) + strlen(pszSrc);

      pszTemp = (char*)realloc(pszDest, nLen + 1);
      if (pszTemp) {
         pszDest = pszTemp;
         strcat(pszDest, pszSrc);
         pszDest[nLen] = '\0';
      }
      else {
         msSetError(MS_MEMERR, "Error while reallocating memory.", "strcatalloc()");
         return NULL;
      }        
   }
   
   return pszDest;
}

char *msJoinStrings(char **array, int arrayLength, const char *delimeter) 
{
  char *string;
  int stringLength=0;
  int delimeterLength;
  int i;

  if(!array || arrayLength <= 0 || !delimeter) return NULL;

  delimeterLength = strlen(delimeter);

  for(i=0; i<arrayLength; i++)
    stringLength += strlen(array[i]) + delimeterLength;

  string = (char *)calloc(stringLength+1, sizeof(char));
  if(!string) return NULL;

  for(i=0; i<arrayLength-1; i++) {
    strcat(string, array[i]);
    strcat(string, delimeter);
  }
  strcat(string, array[i]); // add last element, no delimiter

  return string;
}

#define HASH_SIZE  16
/*
 * Return a hashed string for a given input string.
 * The caller should free the return value.
*/
char *msHashString(const char *pszStr)
{
    unsigned char sums[HASH_SIZE] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
    char *pszOutBuf = NULL;
    int i=0;

    pszOutBuf = (char*)malloc( (HASH_SIZE*2+1)*sizeof(char) );
    if (pszOutBuf == NULL)
    {
        // msSetError(MS_MEMERR, ...);
    }

    for(i=0; pszStr && pszStr[i]; i++)
    {
        sums[i%HASH_SIZE] += (unsigned char)(pszStr[i]);
    }

    for(i=0; i<HASH_SIZE; i++)
    {
        sprintf(pszOutBuf + i*2, "%02x", sums[i]);
    }

    return pszOutBuf;
}
