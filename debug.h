#ifndef DEBUG_GUARD
#define DEBUG_GUARD

# include <stdint.h>
# include <stdlib.h>

# ifdef DEBUG
/* meh */
extern void rawPrint (const char *s, size_t len);

#  define BFMT "%c%c%c%c%c%c%c%c"
#  define B(byte)        \
  (byte & 0x80 ? '1' : '0'), \
  (byte & 0x40 ? '1' : '0'), \
  (byte & 0x20 ? '1' : '0'), \
  (byte & 0x10 ? '1' : '0'), \
  (byte & 0x08 ? '1' : '0'), \
  (byte & 0x04 ? '1' : '0'), \
  (byte & 0x02 ? '1' : '0'), \
  (byte & 0x01 ? '1' : '0')
#  define DEBUGLN(f, ...)                                       \
  do { fprintf (stdout, f "\n", ##__VA_ARGS__); }               \
  while (0)

#  define DEBUG_INSTRUCTION_LOAD() do {                                 \
  char buffer[INSTRUCTION_SIZE+1];                                      \
  buffer[INSTRUCTION_SIZE] = '\0';                                      \
  debug_byte (instr, buffer, INSTRUCTION_SIZE);                         \
  const char *opname = OP_NAME (tmp->rator);                            \
  DEBUGLN (" I: %s, RATOR: " BFMT                                       \
           " (\033[1;32m%17s\033[0m), RAND: " BFMT " (%d)",             \
           buffer,                                                      \
           B (tmp->rator),                                              \
           opname ? opname : "HALT",                                    \
           B (tmp->u32),                                                \
           UOPERAND0 (tmp));                                            \
  } while (0)

#  define DEBUG_INSTRUCTION_NEXT() do {                                 \
    const char *opname = OP_NAME (pc->rator);                           \
    DEBUGLN ("\033[1;32m # %-17s\033[0m RATOR: " BFMT ", RAND: " BFMT " (%d)", \
             opname ? opname : "HALT", B (pc->rator),                   \
             B (pc->u32),  UOPERAND0 (pc));                             \
  } while (0)

#  define DEBUG_FAILSTATE() do {                                \
    printf (" \033[1;31m# FAIL[");                               \
    rawPrint (i, strlen (i));                                   \
    printf ("]\033[0m");                                        \
    DEBUGLN ("     NEXT: %s", OP_NAME ((*(pc)).rator));         \
  } while (0)

#  define DEBUG_FAILSTATE2() do {                               \
    printf ("       FAIL["); valPrint (l); printf ("]");        \
    DEBUGLN ("         NEXT: %s", OP_NAME ((*(pc)).rator));     \
  } while (0)

#  define DEBUGL(m) do {                        \
    printf ("         %s[", m);                 \
    valPrint(l);                                \
    printf ("]\n");                             \
  } while (0)

#  define DEBUG_STACK()                                                 \
  do {                                                                  \
    DEBUGLN ("  \033[37mSTACK: %p %p\033[0m",                           \
             (void *) sp, (void *) m->stack);                           \
    mStackFrame *_tmp_bt; uint32_t _ii;                                 \
    for (_ii = 1, _tmp_bt = sp - 1; _tmp_bt > m->stack; _tmp_bt--, _ii++) { \
      printf ("   \033[37m %i. pc:%p i:`", _ii, (void *) _tmp_bt->pc);  \
      if (_tmp_bt->i) rawPrint (_tmp_bt->i, strlen (_tmp_bt->i));       \
      printf ("`, ir:`");                                               \
      if (_tmp_bt->ir) rawPrint (_tmp_bt->ir, strlen (_tmp_bt->ir));                     \
      DEBUGLN ("`\033[0m");                                             \
    }                                                                   \
    DEBUGLN ("");                                                       \
  } while (0)

#  define DEBUG_PUSH(__sp)                                              \
  do {                                                                  \
    printf ("  PUSH(%p, '", (void*)(__sp->pc));                         \
    if (__sp->i) rawPrint (__sp->i, strlen (__sp->i));                  \
    printf ("')");                                                      \
  } while (0);

#  define DEBUG_PUSHLR(__sp)                                            \
  do {                                                                  \
    printf ("  PUSHLR(%p, %p, '",                                       \
            ((void*) (__sp->pc)),                                       \
            ((void*) (__sp->pcN)));                                     \
    if (__sp->i) rawPrint (__sp->i, strlen (__sp->i));                  \
    printf ("', '");                                                    \
    if (__sp->ir) rawPrint (__sp->ir, strlen (__sp->ir));               \
    printf ("', %d)\n", __sp->k);                                       \
  } while (0);

# else  /* TEST */
#  define DEBUGLN(f, ...)
#  define DEBUG_INSTRUCTION_NEXT()
#  define DEBUG_INSTRUCTION_LOAD()
#  define DEBUG_FAILSTATE()
#  define DEBUG_FAILSTATE2()
#  define DEBUGL(m)
#  define DEBUG_STACK()
#  define DEBUG_PUSH(__sp)
#  define DEBUG_PUSHLR(__sp)
# endif  /* TEST */

static inline char *debug_byte (uint32_t a, char *buffer, int size) {
  buffer += size - 1;
  for (int i = 31; i >= 0; i--, a >>=1)
    *buffer-- = (a & 1) + '0';
  return buffer;
}

#endif  /* DEBUG_GUARD */
