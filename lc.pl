/*

Universidade da Madeira
Faculdade de Ciências Exatas e da Engenharia
Lógica Computacional
Trabalho de avaliação
2017/2018

*/

/* A lista tem um elemento igual a X? 
* Exemplo de input do predicado -> membro(1,[2,1]).
* */

membro(X,[X|_]).
membro(X,[_|C]):- membro(X,C).

/* A lista elimina X, sse X estiver na lista
* Exemplo de input do predicado -> elimina(1,[5,1],X). ou elimina(1,[5,1],[5].
* */

elimina(X,[],[]).
elimina(X,[X|L],L1):- elimina(X,L,L1).
elimina(X,[Y|L],[Y|L1]):- not(Y=X), elimina(X,L,L1).

/* Operações lógicas */

:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').

/* Definição de um símbolo proposicional com as operações lógicas */

simb_prop(X):- not(X=neg Y), not(X=Y e Z), not(X=Y ou Z).

/* Definição de um literal */

literal(X):- simb_prop(X).
literal(neg X):- simb_prop(X).

disj(X):- literal(X).
disj(X ou Y):- disj(X), disj(Y).

fnc(X):- disj(X).
fnc(X e Y):- fnc(X), fnc(Y).

/* O predicado converte_imp_aux/2 definido abaixo é (...por ser preenchido) */

converte_imp_aux(L,C):- membro(S,L), membro(X imp Y,S), elimina(S,L,L1), elimina(X imp Y, S, S1), converte_imp_aux([[neg X,Y|S1]|L1],C).

converte_imp_aux(L,C):- membro(S,L), membro(neg(X imp Y),S), elimina(S,L,L1), elimina(neg(X imp Y), S, S1), converte_imp_aux([[X|S1],[neg Y|S1]|L1],C).

converte_imp_aux(L,L).

/* O predicado converte_imp/1 definido abaixo recebe uma expressão sse a mesma tiver uma implicação, a fim de ser simplificada. Grande parte do processo é feito pelo predicado converte_imp_aux/2 definido acima.
* Exemplo de input do predicado -> converte_imp([[p imp q]]).
* !!! NOTA: Não tenho a certeza se o predicado converte_imp/1 tem esta intenção !!! */

converte_imp(L):- converte_imp_aux(L,C), write('A fórmula representada pela lista de listas introduzida é equivalente à fórmula que é representada pela seguinte lista de listas de fórmulas:'), nl, write(C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercício 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Não sei. Dado um input do tipo "p ou q" ou "p imp q" devolve o mesmo input no output e um "true". */

converte_aux(L,C):- membro(S,L), membro(neg neg X,S), elimina(S,L,L1), elimina(neg neg X,S,S1), converte_aux([[X|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X ou Y,S), elimina(S,L,L1), elimina(X ou Y,S,S1), converte_aux([[X,Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X ou Y),S), elimina(S,L,L1), elimina(neg(X ou Y),S,S1), converte_aux([[neg X|S1],[neg Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X e Y,S), elimina(S,L,L1), elimina(X e Y,S,S1), converte_aux([[X|S1],[Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X e Y),S), elimina(S,L,L1), elimina(neg(X e Y),S,S1), converte_aux([[neg X,neg Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X imp Y,S), elimina(S,L,L1), elimina(X imp Y, S, S1), converte_aux([[neg X,Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X imp Y),S), elimina(S,L,L1), elimina(neg(X imp Y), S, S1), converte_aux([[X|S1],[neg Y|S1]|L1],C).

converte_aux(L,L).

converte(L):- converte_aux(L,C), nl, write(C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercício 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercício 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Não sei qual é o input que é suposto dar ao predicado ref/1 %

elimina_rep_novo([[X],[X]],[[]]).
elimina_rep_novo([[X|L],[X|S]],C):- membro([X],[L|S]), elimina_rep_novo([L|S],C).
elimina_rep_novo([[X|L]],C):- not(membro([X],[L])), elimina_rep_novo([L],C).
elimina_rep_novo(L,L).
elimina_rep([X|L],Z):- membro(X,L), elimina_rep(L,Z).
elimina_rep([X|L],[X|Z]):- not(membro(X,L)), elimina_rep(L,Z).

concatena([], B, B).
concatena([X|A], B, [X|L]):-concatena(A, B, L).

converte_neg_aux(L,C):- membro(S,L), membro(neg X,S), elimina(S,L,L1), elimina(neg X,S,S1), converte_aux([[neg neg X|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X e Y,S), elimina(S,L,L1), elimina(X e Y,S,S1), converte_aux([[neg(X e Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X e Y),S), elimina(S,L,L1), elimina(neg(X e Y),S,S1), converte_aux([[neg(neg(X e Y))|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X ou Y,S), elimina(S,L,L1), elimina(X ou Y,S,S1), converte_aux([[neg(X ou Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X ou Y),S), elimina(S,L,L1), elimina(neg(X ou Y),S,S1), converte_aux([[neg(neg(X ou Y))|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X imp Y,S), elimina(S,L,L1), elimina(X imp Y,S,S1), converte_aux([[neg(X imp Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X imp Y),S), elimina(S,L,L1), elimina(neg(X imp Y),S,S1), converte_aux([[neg(neg(X imp Y))|S1]|L1],C).

converte_neg(L):- converte_neg_aux(L,C), nl, write(C).

res_aux(L,C):- membro([X|S1],L), membro([neg X|S2],L), concatena(S1,S2,S3), elimina([X|S1],L,L1), elimina([neg X|S2],L1,L2), append([S3],L2,L3), res_aux(L3,C).
res_aux(L,L).

res(L):- res_aux(L,C), nl, write(C).

ref_aux(L,[[]]):- res_aux(L,[[]]), nl, write('é refutavel').
ref_aux(L,S):- res_aux(L,S), nl, write('não é refutavel').

ref(L):- ref_aux(L,_), res(L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercício 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
