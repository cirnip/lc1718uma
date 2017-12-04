/*

Universidade da Madeira
Faculdade de Ciências Exatas e da Engenharia
Lógica Computacional
Trabalho de avaliação
2017/2018

*/

/* código escrito com base no que foi lido nas sugestões do enunciado */

:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').

simb_prop(X) :- not(X = neg Y), not(X = Y e Z), not(X = Y ou Z).

literal(X) :- simb_prop(X).
literal(neg X) :- simb_prop(X).
