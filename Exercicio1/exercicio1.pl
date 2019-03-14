% Sistemas de Representação de Conhecimento e Raciocínio - Exercicio 1
% Grupo 15

% Manuel Monteiro
% Eduardo Semanas
% Pedro Almeida
% João Vieira

%--------------------------------------------------------------------------------------------
% SICStus PROLOG: Declaracoes iniciais

:- set_prolog_flag(discontiguous_warnings,off).
:- set_prolog_flag(single_var_warnings,off).
:- set_prolog_flag(unknown,fail).


%--------------------------------------------------------------------------------------------
% Definição de Invariante

:- op(900,xfy,'::').

% -------------------------------------------------------------------------------------------
% BASE DE CONHECIMENTO
%--------------------------------------------------------------------------------------------
% Base de conhecimento com informação sobre utentes, servicos e consultas

:- dynamic(utente/4).
:- dynamic(servico/4).
:- dynamic(consulta/4).

%--------------------------------------------------------------------------------------------
% Extensao do predicado utente: #IdUt, Nome, Idade, Cidade -> {V,F}

utente(1,'Pedro Oliveira',60,'Braga').
utente(2,'José Pedro Morais',50,'Braga').
utente(3,'José Maria Araújo ',45,'Braga').
utente(4,'Maria dos Santos',12,'Vieira do Minho').
utente(5,'Rui Pereira',27,'Povoa de Varzim').
utente(6,'Rui Vieira',24,'Povoa de Lanhoso').
utente(7,'Marta Santos',55,'Lisboa').
utente(8,'André Sales',23,'Lisboa').
utente(9,'João Pereira',22,'Lisboa').
utente(10,'Diogo Soares',18,'Lisboa').
utente(11,'Rita Oliveira',70,'Porto').
utente(12,'Ana Rita Sousa',43,'Porto').
utente(13,'Beatriz Cunha',22,'Porto').
utente(14,'Ana Beatriz de Oliveira',32,'Setubal').
utente(15,'Augusto da Silva',44,'Faro').

%--------------------------------------------------------------------------------------------
% Extensao do predicado servico: #IdServ, Descricao, Instituicao, Cidade -> {V,F}

servico(1,'Cardiologia','Hospital de Braga','Braga').
servico(2,'Pediatria','Hospital de Privado de Braga','Braga').
servico(3,'Urgência','Hospital de Braga','Braga').
servico(4,'Ortopedia','Hospital de Braga','Braga').
servico(5,'Oncologia','IPO','Porto').
servico(6,'Urgência','Hospital de Santa Maria','Porto').
servico(7,'Maternidade','Hospital de Braga','Braga').
servico(8,'Neurologia','Centro Hospitalar Sao Joao','Porto').
servico(9,'Oftalmologia','Hospital de Braga','Braga').
servico(10,'Urgência','Centro Hospitalar de Lisboa Central','Lisboa').
servico(11,'Urgência','Hospital Lusiadas','Faro').
servico(12,'Otorrinolaringologia','Hospital da Luz','Lisboa').

%--------------------------------------------------------------------------------------------
% Extensao do predicado consulta: Data, #IdUt, #IdServ, Custo -> {V,F}

consulta('2011-12-12',1,1,55.0).
consulta('2012-3-12',1,1,55.0).
consulta('2012-10-1',2,1,55.0).
consulta('2013-5-23',6,4,45.0).
consulta('2014-1-18',5,6,0.0).
consulta('2014-2-7',9,12,20.50).
consulta('2015-1-2',15,11,0.0).
consulta('2015-4-4',11,8,80.50).
consulta('2015-7-25',15,11,0.0).
consulta('2015-9-5',14,12,20.50).
consulta('2016-5-30',12,5,75.50).
consulta('2016-9-5',4,2,15.0).
consulta('2016-7-28',7,10,0.0).
consulta('2017-2-12',8,10,0.0).
consulta('2017-7-26',3,3,0.0).
consulta('2017-8-20',10,12,20.50).
consulta('2018-6-15',13,6,0.0).
consulta('2018-6-29',10,12,35.0).
consulta('2018-12-10',10,12,35.0).

%--------------------------------------------------------------------------------------------
% Extensao do predicado solutions: X, Z, Lista -> {V,F} 

solutions(X,Y,Z) :- findall(X,Y,Z).

%--------------------------------------------------------------------------------------------

% Extensao do predicado inserir: Termo -> {V,F}
inserir(T) :- assert(T).
inserir(T) :- retract(T),!,fail.

% Extensao do predicado remover: Termo -> {V,F}
remover(T) :- retract(T).

% Extensao do predicado teste: Lista -> {V,F}
teste([]).
teste([H|T]) :- H, teste(T).

% Extensao do predicado que permite evolucao do conhecimento: Termo -> {V,F}
evolucao(T) :- solutions(I,+T::I,L),
		inserir(T),
		teste(L).

% Extensao do predicado que permite involucao do conhecimento: Termo -> {V,F}
involucao(T) :- solutions(I,-T::I,L),
		teste(L),
		remover(T).

% Extensao do predicado comprimento: Lista, Resultado -> {V,F}
comprimento([],0).
comprimento([H|T],R) :- comprimento(T,L),
		R is 1+L.

%--------------------------------------------------------------------------------------------
% [Invariantes]

% Invariante estrutural do utente (nao permite insercao repetida de um utente)
+utente(ID,N,I,C) :: (solutions(ID,utente(ID,N,I,C),L),
					comprimento(L,R),
					R == 1).

% Invariante estrutural do utente (controla a remocao de um utente)
-utente(ID,N,I,C) :: (solutions(ID,utente(ID,N,I,C),L),
					comprimento(L,R),
					R == 1).

% Invariante estrutural do servico (nao permite insercao repetida de um servico)
+servico(IDs,D,I,C) :: (solutions(IDs,(servico(IDs,_,_,_)),L),
					comprimento(L,R),
					R == 1).

% Invariante estrutural do servico (controla a remocao de um servico)
-servico(IDs,D,I,C) :: (solutions(IDs,(servico(IDs,D,I,C)),L),
					comprimento(L,R),
					R == 1).

% Invariante estrutural da consulta (nao permite insercao repetida de uma consulta)
+consulta(D,IDu,IDs,C) :: (solutions((D,IDu,IDs,C),(consulta(D,IDu,IDs,C)),L),
					comprimento(L,R),
					R == 1).

% Invariante estrutural da consulta (nao permite insercao de uma consulta cujo id
% 				           de utente e servico nao existem na base de conhecimento)
+consulta(D,IDu,IDs,C) :: (utente(IDu,_,_,_),servico(IDs,_,_,_)).

% Invariante estrutural da consulta (controla a remocao de uma consulta)
-consulta(D,IDu,IDs,C) :: (solutions((D,IDu,IDs,C),(consulta(D,IDu,IDs,C)),L),
					comprimento(L,R),
					R == 1).

% --------------------------------------------------------------------------------------------
% [Query 1] Registar utentes, servicos e consultas

% Extensao do predicado registaUtente: T -> {V,F}
registaUtente(ID,N,I,C) :- evolucao(utente(ID,N,I,C)).

% Extensao do predicado registaServico: T -> {V,F}
registaServico(IDs,D,I,C) :- evolucao(servico(IDs,D,I,C)).

% Extensao do predicado registaConsulta: T -> {V,F}
registaConsulta(D,IDu,IDs,C) :- evolucao(consulta(D,IDu,IDs,C)).


% --------------------------------------------------------------------------------------------
% [Query 2] Remover utentes, servicos e consultas

% Extensao do predicado removeUtente: T -> {V,F}
removeUtente(ID) :- involucao(utente(ID,_,_,_)).

% Extensao do predicado removeServico: T -> {V,F}
removeServico(ID) :- involucao(servico(ID,_,_,_)).

% Extensao do predicado removeConsulta: T -> {V,F}
removeConsulta(D,IDu,IDs,C) :- involucao(consulta(D,IDu,IDs,C)).

% --------------------------------------------------------------------------------------------
% [Query 3] Identificar as instituições prestadoras de servicos

% Extensao do predicado instServ: ListaResultado -> {V,F}
instServ(R1) :- solutions((I),servico(_,_,I,_),R),
					apagaRep(R,R1).

% --------------------------------------------------------------------------------------------
% [Query 4] Identificar utentes, servicos e consultas por criterios de selecao

% Extensao do predicado utenteID: ID, Resultado -> {V,F}
utenteID(ID,R)      :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).

% Extensao do predicado utenteNome: Nome, Resultado -> {V,F}
utenteNome(N,R)     :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).

% Extensao do predicado utenteIdade: Idade, Resultado -> {V,F}
utenteIdade(I,R)    :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).

% Extensao do predicado utenteCidade: Cidade, Resultado -> {V,F}
utenteCidade(C,R)   :- (solutions((ID,N,I,C),utente(ID,N,I,C),R)).


% Extensao do predicado servicoID: ID, Resultado -> {V,F}
servicoID(ID,R)     :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).

% Extensao do predicado servicoDesc: Descricao, Resultado -> {V,F}
servicoDesc(D,R)    :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).

% Extensao do predicado servicoInst: Instituicao, Resultado -> {V,F}
servicoInst(I,R)    :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).

% Extensao do predicado servicoCidade: Cidade, Resultado -> {V,F}
servicoCidade(C,R)  :- (solutions((ID,D,I,C),servico(ID,D,I,C),R)).


% Extensao do predicado consultaData: Data, Resultado -> {V,F}
consultaData(D,R)   :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).

% Extensao do predicado consultaIDu: IDutente, Resultado -> {V,F}
consultaIDu(IDu,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).

% Extensao do predicado consultaIDs: IDservico, Resultado -> {V,F}
consultaIDs(IDs,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).

% Extensao do predicado consultaCusto: Custo, Resultado -> {V,F}
consultaCusto(C,R)  :- (solutions((D,IDu,IDs,C),consulta(D,IDu,IDs,C),R)).

% ------------------------------------------------------------------------------------------
% [Query 5] Identificar servicos prestados por instituicao, cidade, data e custo

% Extensao do predicado servInst: Instituicao, Resultado -> {V,F}
servInst(I,R) :- servicoInst(I,R).

% Extensao do predicado servCidade: Cidade, Resultado -> {V,F}
servCidade(C,R) :- servicoCidade(C,R).

% Extensao do predicado servicoData: Data, Resultado -> {V,F}
servicoData(Data,R) :- solutions(servico(IDs,D,I,C),(consulta(Data,_,IDs,_),servico(IDs,D,I,C)),R1),
							apagaRep(R1,R).

% Extensao do predicado servicoCusto: Custo, Resultado -> {V,F}
servicoCusto(Custo,R) :- solutions(servico(IDs,D,I,C),(consulta(_,_,IDs,Custo),servico(IDs,D,I,C)),R1),
							apagaRep(R1,R).

% -------------------------------------------------------------------------------------------
% [Query 6] Identificar os utentes de um servico ou instituicao

% Extensao do predicado utenteServ: Descricao, Resultado -> {V,F}
utenteServ(D,R) :- solutions((utente(I,N,IDA,CI),Inst),(servico(IDS,D,Inst,_), consulta(_,I,IDS,_),utente(I,N,IDA,CI)),R).
					
% Extensao do predicado utenteInst: Instituicao, Resultado -> {V,F}
utenteInst(INS,R) :- solutions((utente(I,N,IDA,CI),servico(D)),(servico(IDS,D,INS,_), consulta(_,I,IDS,_),utente(I,N,IDA,CI)),R).

% -------------------------------------------------------------------------------------------
% [Query 7] Identificar servicos realizados por utente, instituicao e cidade

% Extensao do predicado que procura o nome de utente dado o seu ID 
% nomeUtente: IDutente, Resultado -> {V,F}
nomeUtente(IDu,R) :- solutions(N,utente(IDu,N,_,_),R).

% Extensao do predicado servicosByUtente: IDutente, Resultado -> {V,F}
servicosByUtente(IDu,R) :- solutions(servico(IDs,D),(consulta(_,IDu,IDs,_),servico(IDs,D,_,_),utente(IDu,_,_,_)),R1),
							nomeUtente(IDu,L),
							append(L,R1,R).

% Extensao do predicado servicosByInst: Instituicao, Resultado -> {V,F}
servicosByInst(Inst,R) :- solutions(servico(IDs,D),servico(IDs,D,Inst,_),R1),
							append([Inst],R1,R).

% Extensao do predicado servicosByCidade: Cidade, Resultado -> {V,F}
servicosByCidade(Cid,R) :- solutions(servico(IDs,D),servico(IDs,D,_,Cid),R1),
							append([Cid],R1,R).

% -------------------------------------------------------------------------------------------
% [Query 8] Calcular custo total dos cuidados de saude por utente, servico, instituicao e data 

% Extensao do predicado custoByUtente: IDutente, Resultado -> {V,F}
custoByUtente(IDu,R) :- solutions(C,consulta(_,IDu,_,C),R1),
							somaCustos(R1,R).

% Extensao do predicado custoByServ: IDservico, Resultado -> {V,F}
custoByServ(IDs,R) :- solutions(C,consulta(_,_,IDs,C),R1),
							somaCustos(R1,R).

% Extensao do predicado custoByInst: Instituicao, Resultado -> {V,F}
custoByInst(Inst,R) :- solutions(C,(servico(IDs,_,Inst,_),consulta(_,_,IDs,C)),R1),
							somaCustos(R1,R).

% Extensao do predicado custoByData: Data, Resultado -> {V,F}
custoByData(Data,R) :- solutions(C,consulta(Data,_,_,C),R1),
							somaCustos(R1,R).

%--------------------------------------------------------------------------------------------
% [Auxiliar] Funções adicionais para tratamentos de dados

% Extensao do predicado que apaga todas ocorrencias de 1 elemento numa lista
% apaga1: Elemento, Lista, ListaResultado -> {V,F}
apaga1(_,[],[]).
apaga1(X,[X|Y],T):- apaga1(X,Y,T).
apaga1(X,[H|Y],[H|R]) :- apaga1(X,Y,R).

% Extensao do predicado que apaga todos os elementos repetidos de uma lista
% apagaRep: Lista, ListaResultado -> {V,F}
apagaRep([],[]).
apagaRep([X|Y],[X|L1]) :- apaga1(X,Y,L), apagaRep(L,L1).

% Extensao do predicado que concatena duas listas
% append: Lista1, Lista2, ListaResultado -> {V,F}
append([],X,X).
append([X|Y],Z,[X|W]) :- append(Y,Z,W).

% Extensao do predicado que soma uma lista de numeros
% somaCustos: Lista, Resultado -> {V,F}
somaCustos([X],X).
somaCustos([H|T],R) :- somaCustos(T,L), R is H+L.

