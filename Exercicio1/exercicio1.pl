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
utente(2,'Joe',50,'Braga').


%--------------------------------------------------------------------------------------------
% Extensao do predicado servico: #IdServ, Descricao, Instituicao, Cidade -> {V,F}

servico(1,'Maternidade','Hospital de Braga','Braga').


%--------------------------------------------------------------------------------------------
% Extensao do predicado consulta: Data, #IdUt, #IdServ, Custo -> {V,F}

consulta('2018-12-10',1,1,60.50).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que realiza a procura de conhecimento

solutions(X,Y,Z) :- findall(X,Y,Z).

% Query 3--------------------------------------------------------------------------------------------
% Extensao do predicado que calcula as instituições que realizam serviços

instServ(R1) :- solutions((I),servico(ID,D,I,C),R),
					apagaRep(R,R1).


% Query 4------------------------------------------------------------------------------------
% Extensao do predicado que identifica utentes por criterios de selecao

utenteID(ID,R)      :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).
utenteNome(N,R)     :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).
utenteIdade(I,R)    :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).
utenteCidade(C,R)   :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica servicos por criterios de selecao

servicoID(ID,R)     :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).
servicoDesc(D,R)    :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).
servicoInst(I,R)    :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).
servicoCidade(C,R)  :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica consultas por criterios de selecao

consultaData(D,R)   :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).
consultaIDu(IDu,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).
consultaIDs(IDs,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).
consultaCusto(C,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).

% Query 5------------------------------------------------------------------------------------
% Extensao do predicado que identifica servicos por Instituicao

servInst(I,R) :- servicoInst(I,R).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica servicos por Cidade

servCidade(C,R) :- servicoCidade(C,R).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica servicos por Data

servicoData(Data,R) :- solutions(servico(IDs,D,I,C),(consulta(Data,_,IDs,_),servico(IDs,D,I,C)),R1),
							apagaRep(R1,R).

%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica servicos por Custo

servicoCusto(Custo,R) :- solutions(servico(IDs,D,I,C),(consulta(_,_,IDs,Custo),servico(IDs,D,I,C)),R1),
							apagaRep(R1,R).

% Query 6-------------------------------------------------------------------------------------------
% Extensao do predicado que identifica utentes por Servico

utServ(D,R) :- solutions((utente(I,N,IDA,CI),Inst),(servico(IDS,D,Inst,_), consulta(_,I,IDS,_),utente(I,N,IDA,CI)),R).
					
					
%--------------------------------------------------------------------------------------------
% Extensao do predicado que identifica utentes por Instituicao

utInst(INS,R) :- solutions((utente(I,N,IDA,CI),servico(D)),(servico(IDS,D,INS,_), consulta(_,I,IDS,_),utente(I,N,IDA,CI)),R).


%--------------------------------------------------------------------------------------------
% funções adicionais para tratamentos de dados:

% Extensao do predicado que apaga todas ocorrencias de 1 elemento numa lista
% apaga1: Elemento, Lista, ListaResultado -> {V,F}

apaga1(_,[],[]).
apaga1(X,[X|Y],T):- apaga1(X,Y,T).
apaga1(X,[H|Y],[H|R]) :- apaga1(X,Y,R).

% Extensao do predicado que apaga todos os elementos repetidos de uma lista
% apagaRep: Lista, ListaResultado -> {V,F}

apagaRep([],[]).
apagaRep([X|Y],[X|L1]) :- apaga1(X,Y,L), apagaRep(L,L1).





