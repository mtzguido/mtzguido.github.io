/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: krml -skip-compilation -warn-error +9 out.krml
  F* version: 58c915a8
  KaRaMeL version: 22425a93
 */

#ifndef __Tuto_H
#define __Tuto_H

#include "krmllib.h"

extern uint32_t Tuto_x;

extern uint32_t Tuto_x_real;

extern uint32_t Tuto_x_shifted;

void Tuto_f(void);

void Tuto_incr(uint32_t *r, uint32_t *other);

void Tuto_call_incr(void);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__uint32_t_tags;

typedef struct FStar_Pervasives_Native_option__uint32_t_s
{
  FStar_Pervasives_Native_option__uint32_t_tags tag;
  uint32_t v;
}
FStar_Pervasives_Native_option__uint32_t;

FStar_Pervasives_Native_option__uint32_t Tuto_sum_low(uint32_t *b, uint32_t len);

bool Tuto_sum_low2(uint32_t *uu___, uint32_t *uu___1, uint32_t uu___2);


#define __Tuto_H_DEFINED
#endif
