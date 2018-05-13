% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
%     1.1 Reading an input string and convert it to a tokenized list
%     1.2 Processing tokenized list
% ===========================================================
%parse([every,white,container,on,the,bottom,shelf,contains,a,banana],X).
chat:-
 repeat,
   readinput(Input),
   process(Input),
  (Input = [bye| _] ),!.


% ===========================================================
% Read input:
% 1. Read char string from keyboard.
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
  parse(Input,SemanticRepresentation),
  modelchecker(SemanticRepresentation,Evaluation),
  respond(Evaluation),!,
  nl,nl.

process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

parse(Input, SemanticRepresentation):- sr_parse(Input,SemanticRepresentation).

sr_parse([]).
sr_parse(Sentence,SemanticRepresentation):-
        srparse([],Sentence,SemanticRepresentation).

srparse([X],[],SemanticRepresentation):-
  numbervars(X,0,_),
  SemanticRepresentation = X.
  %write(X).

srparse([Z,Y,X|MoreStack],Words,SemanticRepresentation):-
       rule(LHS,[X,Y,Z]),
       srparse([LHS|MoreStack],Words,SemanticRepresentation).

srparse([Y,X|MoreStack],Words,SemanticRepresentation):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words,SemanticRepresentation).

srparse([X|MoreStack],Words,SemanticRepresentation):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words,SemanticRepresentation).

srparse(Stack,[Word|Words],SemanticRepresentation):-
        lex(X,Word),
        srparse([X|Stack],Words,SemanticRepresentation).


% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================
% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------

lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).

%lemma(the,dt).
%lemma(no,dt).

lemma(the,dt).
lemma(no,dtnot).

lemma(not,vnot).

lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).

lemma(burger,n).
lemma(ham,n).
lemma(box,n).
lemma(banana,n).
lemma(bowl,n).
lemma(container,n).
lemma(egg,n).
lemma(freezer,n).
lemma(fridge,n).
lemma(meat,n).
lemma(milk,n).
lemma(popsicles,n).
lemma(sandwich,n).
lemma(shelf,n).
lemma(watermelon,n).

lemma(tom,pn).
lemma(jose,pn).
lemma(sue,pn).
lemma(alba,pn).
lemma(john,pn).
lemma(mia,pn).
lemma(sam,pn).

lemma(almond,adj).
lemma(empty,adj).
lemma(red,adj).
lemma(green,adj).
lemma(blue,adj).
lemma(white,adj).
lemma(top,adj).
lemma(bottom,adj).
lemma(middle,adj).
lemma(yellow,adj).

lemma(one,number).
lemma(two,number).

lemma(is,be).
lemma(was,be).
lemma(are,be).

lemma(eat,tv).
lemma(ate,tv).
lemma(drink,tv).
lemma(drank,tv).
lemma(drunk,tv).
lemma(drinks,tv).
lemma(contain,tv).
lemma(is,tv).

lemma(has,tv).
lemma(had,tv).
lemma(have,tv).

lemma(belongs,pv).
lemma(rely,pv).

lemma(did,aux).
lemma(does,aux).

lemma(put,dtv).
lemma(puts,dtv).

lemma(that,rel).
% WH questions vs REL, how to figure ambiguity/
% lemma(who,rel).
% lemma(what,rel).
% lemma(which,rel).

lemma(in,p).
lemma(under,p).
lemma(below,p).
lemma(inside,p).
lemma(on,p).

lemma(on,vacp).
lemma(to,vacp).
lemma(there,vacp).
lemma(there,vacp_).

lemma(who,whpr).
lemma(which,whpr).
lemma(what,whpr).


lemma(Word,Tag,Stem) :- atom_chars(Word, WordList),
                   lemma(Stem,Tag),
                   atom_chars(Stem, LemmaList),
                   compare_lemma(WordList,LemmaList),!.

compare_lemma(_,[]).
compare_lemma([W|WordList],[W|LemmaList]) :-
                  compare_lemma(WordList,LemmaList).
% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------

%[every blue container on the top shelf contains a sandwich that has no meat]
%[every white container on the bottom shelf contains a banana] (works)
% [a,blue,box,contains,ham]
% [a,blue,box,contains,some,ham]
% [the,white,box,that,the,freezer,contains,belongs,to,sue]
% is,there,an,egg,inside,the,blue,box
% are,there,two,eggs,inside,the,blue,box
% what,does,the,green,box,contain
% who,put,every,yellow,box,on,the,white,bowl


lex(pn( (P)^X ),Word):-
    lemma(Word,pn),
    P=..[^,Word,X].

%lex(X,blue)
lex(adj((X^P)^X^and(P,Q)),Word):-
    lemma(Word,adj),
    Q =.. [Word,X].

%lex(X,two)
lex(num((X^P)^X^and(P,Q)),Word):-
    lemma(Word,num),
    Q =.. [Word,X].

%rc(), n(_4686^meat(_4686))

%sr_parse([what,does,the,green,box,contain])
%lex(A,what), lex(B,does),lex(C,the), lex(D,green), lex(E,box), lex(F,contain),
%rule(P,[D,E]), rule(Q,[C,P]), rule(R,[F]), rule(S,[R]).


%sr_parse([tom,put,a,box,on,the,bowl])


lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),Word):-
    lemma(Word,dtexists).

%lex(X,that).
lex(rel([]), Word):- lemma(Word,rel).

lex(dt((X^P)^(X^Q)^Z),Word):-
   lemma(Word,dt),
    A = and(P,Q),
    Z =..[Word,X,A].

lex(dtnot((X^P)^(X^Q)^not(X,(and(P,Q)))),Word):-
   lemma(Word,dtnot).

%lex(X,on)

lex(vacp([]),Word) :- lemma(Word,vacp).
%tryng special case like there on questions
lex(vacp_([]),Word) :- lemma(Word,vacp_).

lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word) :-
  lemma(Word,p),
  Z =.. [Word,X,Y].

lex(p(X^Y^P),Word) :-
  lemma(Word,p),
  P =.. [Word,X,Y].



%lex(tv(X^Y^Z,[]), Word):-
%      lemma(Word,tv),
%      Z =..[Word,X,Y].

%lex(n(X^P),Word):-
% lemma(Word,n),
% P=.. [Word,X].

lex(X, Word):-
      lemma(Word,aux),
      X = aux.

lex(X, Word):-
      lemma(Word,be),
      X = be.

lex(whpr((X^Y)^P),Word) :- lemma(Word,whpr), P=..[Word,X,Y].

lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-
    lemma(Word,dtforall).

%Last resource is to stem the word
%Stemming for verb
lex(tv(X^Y^Z,[]), Lemma):-
      lemma(Lemma,tv,Stem),
      Z =..[Stem,X,Y].

%In case of questions
lex(tv(X^Y^Z,[]), Lemma):-
      lemma(Lemma,tv,Stem),
      Z =..[Stem,Y,X].

lex(pv(X^Y^Z,[]), Lemma):-
      lemma(Lemma,pv,Stem),
      Z =..[Stem,X,Y].

lex(dtv(W^X^Y^Z,[]), Lemma):-
      lemma(Lemma,dtv,Stem),
      Z =..[Stem,W,X,Y].

%Stemming for noun
%lex(X,egg)
lex(n(X^P),Lemma):-
  lemma(Lemma,n,Stem),
  P=.. [Stem,X].

% (X^Q)^exists(X,and(egg(X),Q))

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

%sr_parse([the,white,box,that,the,freezer,contains,belongs,to,sue]).

% lex(A,the),lex(B,white),lex(C,box),lex(D,that),lex(E,the),
% lex(F,freezer),lex(G,contains),lex(H,belongs),lex(I,to),lex(J,sue),
% rule(K,[J]), rule(L,[H,I]), rule(M,[G]),.

rule(vp(X^Z,[]),[dtv(A^B^X^Z,[]),np(Y^B),pp(Y^A)]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
rule(ynq(Y),[be, np(X^Y),pp(X)]).

%RC -> REL VP
rule(rc(X,[]),[rel([]),vp(X,[])]).

rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).

% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).

% NP -> No N
rule(np(Y),[dtnot(X^Y),n(X)]).

% NP ->N
rule(np((X^Q)^exists(X,and(P,Q))),[n(X^P)]).

% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
% N -> Adj N
rule(n(Y),[adj(X^Y),n(X)]).
% N -> Num N
rule(n(Y),[num(X^Y),n(X)]).

% NP -> PN
rule(np(X),[pn(X)]).

%PP --> P NP (for other type of p)
rule(pp(X^K),[p(X^Y),np(Y^K)]).
% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).
% PP -> vacp NP
rule(pp(X^Y),[vacp([]),np(X^Y)]).
% NP -> VACP_ np
rule(np(X^Y),[vacp_([]),np(X^Y)]).
% VP -> IV
rule(vp(X,[]),[iv(X,[])]).
% VP -> TV NP
%rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).

% IV -> TV
rule(iv(Y,[X]),[tv(X^Y,[])]).

rule(vp(X,[]),[pv(X,[]),vacp(_)]).


%New Question rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(X,[WH]),[vp(X,[WH])]).

% WH QUESTIONS rules
rule(Y,[whpr(X^Y),vp(X,[])]).
rule(Z,[whpr(Y^Z), ynq(Y)]).
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).

%which milk did sam drink
rule(Z,[whpr((X^Y)^Z), n(X^_), inv_s(Y,[X])]).

%S -> AUX NP VP
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

%Transform What into Q
rule(q(exists(A,and(thing(A),X))),[what(A,X)]).
rule(q(exists(A,and(person(A),X))),[who(A,X)]).
rule(q(exists(A,and(thing(A),X))),[which(A,X)]).

%rule(q(A,and(thing(A),X)),[who(A,rely(john,B))]).


%rule(vp(X^W),[tv(X^Y),n(Y^W)]).

% VP -> DTV NP NP eg: I gave Sue a burger

% VP -> DTV NP PP eg: sam put every yellow box on the white bowl

% sr_parse([tom,put,a,box,on,the,bowl])

%lex(W,tom), lex(X,eat), lex(Y,a), lex(Z,burger).
% dtv(W^A^B^ put(W,X,Y), []).
% np( (A^B) ^the(A,and(burger(A),B)))
% pp( (A^B) ^ and(B,the(C,and(and(box(C),white(C)),on(A,C)))) )

% VP -> VP PP eg: The top shelf contains eggs in a box
% VP -> SV S eg:
% VP -> ADV VP eg:
% VP -> AUX VP eg:
% DT -> NP POS do we need to handle this? POS->s eg: The upper shelf contains Sam's box

% S -> NP VP eg: The white container contains egg
rule(s(Y),[np(X^Y),vp(X,_)]).

% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

% model(...,...)
model([sam1,box1,box2,egg1,egg2,blue1,blue2,milk1,ham1],[
                      [person,[sam1]],
                      [thing,[box1,box2,milk1,almond1,ham1]],
                      [box,[box1,box2]],
                      [blue,[box1]],
                      [milk,[milk1]],
                      [almond,[milk1]],
                      [sam,[sam1]],
                      [ham,[ham1]],
                      [egg,[egg1,egg2]],
                      [contain,[[box2,ham1],[box1,egg1],[box1,egg2],[box2,egg1]]],
                      [drank,[[sam1,milk1]]]
                      ]).

% is_a rule: Ontology
%is_a(sam,person).
%is_a(tom,person).
%is_a(box,thing).
%is_a(milk,thing).
%is_a(ham,thing).
%is_a(ham,meat).

% ==================================================
% Function i
% Determines the value of a variable/constant in an assignment G
% ==================================================

i(Var,G,Value):-
    var(Var),
    member([Var2,Value],G),
    Var == Var2.

i(C,_,Value):-
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a Predicate/Relation
% ==================================================

f(Symbol,Value):-
   model(_,F),
    member([Symbol,ListOfValues],F),
    member(Value,ListOfValues).


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).

% ==================================================
% Sentence
% ==================================================

sat(G1,s(Formula1),G2):-
   sat(G1,Formula1,G),write(G),
   (G==[] -> G2 = [not_true_in_the_model];
      G2 = [true_in_the_model]).

% ==================================================
% Yes-No Question
% ==================================================

sat(G1,ynq(Formula1),G2):-
   sat(G1,Formula1,G),
   (G==[] -> G2 = [no_to_question];
      G2 = [yes_to_question]).

% ==================================================
% WH Question
% ==================================================

sat(G1,q(X,Formula1),G2):-
   sat(G1,exists(X,Formula1),[_,[_,Ans]]),
   model(_,G),findall(V,(member([V,C],G), member(D,C), Ans == D),G2).

% ==================================================
% Numeric quantifiers
% ==================================================

sat(G1,one(X,Formula),G3):-
   sat(G1,exists(X,Formula),G3),write(G3).
%  [_,[Key,Val]] model(B,G),findall(V,(member([V,C],G), member(D,C), Ans == D),G2).

% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).

% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value),
   \+ ( ( sat(G1,exists(X,A),G2), i(X,G2,Value2), \+(Value = Value2)) ).

% ==================================================
% Negation
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).

% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2),
  sat(G2,Formula2,G3).


% ==================================================
% Disjunction
% ==================================================


sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% ==================================================

sat(G,Predicate,G):-
   Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).

% ==================================================
% Sat rule for the
% ==================================================

sat(G1, the(X,Formula),G2):-
  sat(G1,exists(X,Formula),G2).

% ==================================================
% Model Checker
% ==================================================

% check output of sat, if s and sat output is not empty, send [true_in_the_model]
modelchecker(SemanticRepresentation, Evaluation):-
    sat([],SemanticRepresentation,Evaluation).


% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :-
    Evaluation = [true_in_the_model],
    write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :-
    Evaluation = [not_true_in_the_model],
    write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :-
    Evaluation = [yes_to_question],
    write('yes').

% Yes-No interrogative false in the model
respond(Evaluation) :-
    Evaluation = [no_to_question],
    write('no').

% wh-interrogative false in the model
% ...
respond(Evaluation) :-
  Evaluation = [],
  write('Nothing').

% wh-interrogative true in the model
% ...
respond(Evaluation) :-
    findall(_,(member(A,Evaluation),lemma(A,adj),write(A),write(' ')),L1),
    findall(_,(member(A,Evaluation),lemma(A,n),write(A),write(' ')),L2),
    findall(_,(member(A,Evaluation),lemma(A,pn),write(A),write(' ')),L3).
