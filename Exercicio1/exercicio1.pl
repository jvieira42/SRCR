% Sistemas de Representação de Conhecimento e Raciocínio - Exercicio 1
% Grupo 15

% Manuel Monteiro
% Eduardo Semanas
% Pedro Almeida
% João Vieira

%-----------------------------------------------------------------------
% SICStus PROLOG: Declaracoes iniciais

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

%--------------------------------------------------------------------------------------------
% Definição de invariante

:- op(900,xfy,'::').

% -------------------------------------------------------------------------------------------
% BASE DE CONHECIMENTO
%--------------------------------------------------------------------------------------------
% Base de conhecimento com informação sobre cuidado prestado, ato médico , utente


:- dynamic(utente/4).
:- dynamic(servico/4).
:- dynamic(consulta/4).

%--------------------------------------------------------------------------------------------
% Extensao do predicado utente: #IdUt, Nome, Idade, Cidade -> {V,F}

utente(1,'Pedro',60,'Braga').
utente(2,'joe',50,'Braga').


%--------------------------------------------------------------------------------------------
% Extensao do predicado servicos: #IdServ, Descricao, Instituicao, Cidade -> {V,F}

servico(1,'Maternidade','Hospital de Braga','Braga').


%--------------------------------------------------------------------------------------------
% Extensao do predicado consultas: Data, #IdUt, #IdServ, Custo -> {V,F}

consulta('2018-12-10',1,1,60.50).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que realiza a procura de conhecimento

solutions(X,Y,Z) :- findall(X,Y,Z).


