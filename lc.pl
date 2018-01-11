/*

Universidade da Madeira
Faculdade de Ciencias Exatas e da Engenharia
Logica Computacional
Trabalho de avaliacao
2017/2018

*/

/*A fun��o tem como objetivo verificar se X pertence � lista recebida
* Exemplo de input do predicado -> membro(1,[2,1]).
* */
membro(X,[X|_]).
membro(X,[_|C]):- membro(X,C).

/* A funcao elimina X, sse X estiver na lista
* Exemplo de input do predicado -> elimina(1,[5,1],X). ou elimina(1,[5,1],[5].
* */
elimina(X,[],[]).
elimina(X,[X|L],L1):- elimina(X,L,L1).
elimina(X,[Y|L],[Y|L1]):- not(Y=X), elimina(X,L,L1).

/* Operacoes logicas */
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Exemplo de input: converte([[(p e (q ou r)) imp s]]).
* Exemplo de output: [[neg q,neg p, s],[neg r, neg p, s]] */

%Fun��o auxiliar de converte/1
converte_aux(L,C):- membro(S,L), membro(neg neg X,S), elimina(S,L,L1), elimina(neg neg X,S,S1), converte_aux([[X|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X ou Y,S), elimina(S,L,L1), elimina(X ou Y,S,S1), converte_aux([[X,Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X ou Y),S), elimina(S,L,L1), elimina(neg(X ou Y),S,S1), converte_aux([[neg X|S1],[neg Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X e Y,S), elimina(S,L,L1), elimina(X e Y,S,S1), converte_aux([[X|S1],[Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X e Y),S), elimina(S,L,L1), elimina(neg(X e Y),S,S1), converte_aux([[neg X,neg Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(X imp Y,S), elimina(S,L,L1), elimina(X imp Y, S, S1), converte_aux([[neg X,Y|S1]|L1],C).
converte_aux(L,C):- membro(S,L), membro(neg(X imp Y),S), elimina(S,L,L1), elimina(neg(X imp Y), S, S1), converte_aux([[X|S1],[neg Y|S1]|L1],C).
converte_aux(L,L).

converte(L):- converte_aux(L,C), nl, write(C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A função ref/1 é um predicado que recebe uma lista de listas na forma
% clausal e devolve o resultado da aplicação do predicado res/1,
% se o resultado for uma lista vazia escreve que é uma refutação, caso
% contrário escreve que não é uma refutação.

/* Exemplo de input: ref([[a,b,c],[neg b,d],[neg a,d],[neg c,d],[neg d]]).
 * O input acima � refutável. */

/* Outro input: ref([[a,b],[a,neg b],[neg a,b]]).
* O input acima NÃO � refutável.
* NOTA: Este leva mais ou menos 1 minuto para processar pelo interpretador */

% Esta fun��o tem como objetivo receber duas cl�usulas e devolver a
% jun��o de ambas
concatena([], B, B).
concatena([X|A], B, [X|L]):- concatena(A, B, L).

% Esta fun��o tem como objetivo receber uma cl�usula e devolver essa
% mesma cl�usula mas sem vari�veis repetidas
repete([X|C],[X|C1]):- membro(X,C), elimina(X,C,M), repete(M,C1).
repete([X|C],[X|C1]):- not(membro(X,C)), repete(C,C1).
repete([X|[]],[X|[]]).
repete([],[]).

% Esta fun��o tem como objetivo receber duas cl�usulas e devolver a
% cl�usula resolvente dessas mesmas
resolvente([],C,C).
resolvente(C,[],C).
resolvente(C1,C2,C):- membro(X,C1), membro(neg X,C2), elimina(X,C1,C3), elimina(neg X,C2,C4), concatena(C3,C4,C).

% Esta fun��o tem como objetivo receber duas cl�usulas e verificar se
% estas s�o iguais
dif_aux(C1,C2):- membro(X,C1), membro(X,C2), elimina(X,C1,S1), elimina(X,C2,S2), dif_aux(S1,S2).
dif_aux(X,X).

% Esta fun��o tem como objetivo receber duas cl�usulas e verificar se
% estas s�o diferentes
clausulas_difs(C1,C2):- repete(C1,S1), repete(C2,S2), not(dif_aux(S1,S2)).

% Esta fun��o tem como objetivo receber uma cl�usula e uma lista e
% verificar se a cl�usula pertence � lista
pertence(C,L):- membro(L1,L), repete(L1,L2), repete(C,C1), not(clausulas_difs(C1,L2)).

% Esta fun��o tem como objetivo receber uma cl�usula e uma lista e
% verificar se a cl�usula n�o pertence � lista
nao_pertence(C,L):- not(pertence(C,L)).

% Esta fun��o tem como objetivo receber uma lista e devolver uma
% cl�usula/vari�vel que seja resolvente de duas cl�usulas pertencentes �
% lista
resolvente_novo(L,C):- membro(C1,L), membro(C2,L), clausulas_difs(C1,C2), resolvente(C1,C2,C), nao_pertence(C,L).

% Esta fun��o tem como objetivo receber uma lista, devolver uma
% cl�usula/vari�vel que seja resolvente de duas cl�usulas pertencentes �
% lista e f�-lo enquanto escreve duas cl�usulas e a cl�usula
% resolvente de estas
resolvente_novo2(L,C):- membro(C1,L), membro(C2,L), clausulas_difs(C1,C2), resolvente(C1,C2,C), nao_pertence(C,L), nl, write("("), write(C1), write(" , "), write(C2), write(") --> "),write(C).

% Fun��o auxiliar de ref_aux/2 que verifica se uma lista � refut�vel
res_aux(L,C,L2):- resolvente_novo(L,C1), concatena(L,[C1],L1), res_aux(L1,C,L2).
res_aux(L,[],L).

% Fun��o auxiliar de ref_aux/2 para caso que a lista seja refut�vel
res_aux2(L,C,L2):- resolvente_novo2(L,C1), concatena(L,[C1],L1), res_aux2(L1,C,L2).
res_aux2(L,[],L).

% Fun��o auxiliar de ref/1 com duas condi��es, uma para caso que a lista
% seja refut�vel e outra para caso que n�o o seja
ref_aux(L,L1):- res_aux(L,[],L1), membro([],L1), nl, write('Refutavel'), res_aux2(L,[],L1).
ref_aux(L,L1):- res_aux(L,[],L1), not(membro([],L1)), nl, write('Nao e refutavel'), nl, write(L1).

ref(L):- ref_aux(L,L1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A fun��o teorema/1 � um predicado que recebe uma lista de listas,
% verifica se o converte/1 da nega��o de "fi" � refutável e se for
% refut�vel ele devolve que "fi" � teorema no sistema de RP, caso
% contrario diz que n�o � teorema em RP.

/* Exemplo de input: teorema([[(p imp (q imp r)) imp ((p imp q) imp (p imp r))]]).
 * O input acima � um teorema. */

/* Exemplo de input: teorema([[(neg p imp q) imp (p imp q)]]).
 * O input acima n�o � um teorema. */

% Fun��o auxiliar de teorema/1
% converte_neg_aux � um predicado que recebe uma lista de listas L e C
% que � uma lista de listas na forma clausal da nega��o da lista de
% listas L.
% Tem o objetivo semelhante a fun��o converte_aux s� que
% converte_neg_aux realiza a fun��o converte_aux � nega��o da lista
% de listas L assim recebida.

converte_neg_aux(L,C):- membro(S,L), membro(neg X,S), elimina(S,L,L1), elimina(neg X,S,S1), converte_aux([[neg neg X|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X e Y,S), elimina(S,L,L1), elimina(X e Y,S,S1), converte_aux([[neg(X e Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X e Y),S), elimina(S,L,L1), elimina(neg(X e Y),S,S1), converte_aux([[neg(neg(X e Y))|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X ou Y,S), elimina(S,L,L1), elimina(X ou Y,S,S1), converte_aux([[neg(X ou Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X ou Y),S), elimina(S,L,L1), elimina(neg(X ou Y),S,S1), converte_aux([[neg(neg(X ou Y))|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(X imp Y,S), elimina(S,L,L1), elimina(X imp Y,S,S1), converte_aux([[neg(X imp Y)|S1]|L1],C).
converte_neg_aux(L,C):- membro(S,L), membro(neg(X imp Y),S), elimina(S,L,L1), elimina(neg(X imp Y),S,S1), converte_aux([[neg(neg(X imp Y))|S1]|L1],C).

teorema(L):- converte_neg_aux(L,C), res_aux(C,[],C1), membro([],C1), !, write('F e teorema de acordo com o sistema de resolucao proposicional').
teorema(L):- write('F nao e teorema de acordo com o sistema de resolucao proposicional').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exercicio 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
