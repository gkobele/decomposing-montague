
(** %\maketitle% *)

(** * Introduction

   %\citet{DeGroote06}% demonstrates how to give a dynamic
    interpretation to formulae in higher order logic, not by, as is
    done in most works on dynamic semantics, giving a non-standard
    model-theoretic interpretation of such formulae, but rather by
    giving a systematic syntactic translation of these formulae into
    other formulae which, when interpreted in the standard way, are
    equivalent to the dynamic interpretation of the original formulae.
    This is achieved by lifting the types of expressions to be
    functions from left contexts (representing information about
    already established discourse referents) to functions from right
    contexts (representing discourse continuations) to truth values.

   The goal of this short note is to show that the dynamic translation
   of %\citet{DeGroote06}% can be factored into the composition of two
   simpler parts; a left-context translation and a right-context
   translation, or, more precisely, a semantics dealing with dynamism
   without discourse referents, and a semantics dealing with discourse
   referents without dynamism.

   This is a literate Coq document, with source code available on the
   web at %\url{https://github.com/gkobele/decomposing-montague}%.

*)

(* begin hide *)
Section obj.
(* end hide *)
(** * The formal language *)

(** I begin by defining the basic structures of the language.  This
will serve both as a metalanguage (the target language of the
translations) and also as an object language (the source languages of
the translations).

The basic idea of a translation procedure is that an uninterpreted
object language is translated into a language that is already
understand, the meta-language.  The same syntactic forms will be used
(a simple fragment of the lambda calculus) for both.  This offers a
sort of _modularity_ of semantic description.  From the semanticist's
perspective, this means that certain aspects of meaning can be
systematically ignored, knowing that the semantic terms actually
written down are (via the translation process) notational shorthands
for richer meaning representations.  More speculatively, one might
conjecture that each successive translation might have some sort of
deeper reality, perhaps recapitulating the stages of a learner's
semantic language acquisition, or perhaps even as reflective of
different levels of deep semantic analysis of a sentence made as
needed during language processing.

The language is typed, with two basic types; [e] and [t].  Nothing
is assumed about expressions of type [e]; in particular, no expression
of the language will have a type ending in [e].  *)
(* begin hide *)
Variable e : Set.
(* end hide *)
(** In contrast, the type [t], is viewed as the type of complete
propositions, is the locus of recursion in this language.  Thus, [and]
is a binary term forming operator.  There are infinitely many
inhabitants of type [t], many of which are intuitively semantically
equivalent.  There are constants [true] and [false], boolean
connectives [and], [or] and [not], term forming operators [p n] and [r
n] (the [n]th unary and binary relations respectively), and
generalized quantifiers [some], [all] and [pro] (representing a
pronoun).  These provide the basic alphabet for building semantic
terms (of type [t]).  With the exception of [pro], these can be
interpreted in the usual way in higher order models.  [pro] is not
(intended to be understood as) a term in the meta-language, and will
only be given a meaning during the translation process.
%\citet{DeGroote06}% also has a constant _who_, which is however
definable as usual in terms of property conjunction: %\(\textbf{who}\
P\ Q = \lambda x. P x \wedge Q x\)%.  *) 

Inductive t : Set := 
| true : t 
| false : t 
| p : nat -> e -> t 
| r : nat -> e -> e -> t 
| and : t -> t -> t 
| or : t -> t -> t 
| imply : t -> t -> t 
| not : t -> t 
| some : (e -> t) -> t 
| all : (e -> t) -> t 
| pro : (e -> t) -> t.
(** printing false %\ensuremath{\bot}% *)
(** printing true %\ensuremath{\top}% *)
(** printing not %\ensuremath{\neg}% *)
(** printing and %\ensuremath{\wedge}% *)
(** printing or %\ensuremath{\vee}% *)
(** printing imply %\ensuremath{\leadsto}% *)
(** printing some %\textbf{some}% *)
(** printing all %\textbf{all}% *)


(* begin hide *)
Notation "phi 'und' psi" := (and phi psi) (at level 55).
Notation "phi 'oder' psi" := (or phi psi) (at level 60).
Notation "phi 'impl' psi" := (imply phi psi) (at level 65).
Notation "'farmer'" := (p 0).
Notation "'donkey'" := (p 1).
Notation "'laugh'" := (p 2).
Notation "'bray'" := (p 3).
Notation "'own'" := (r 0).
Notation "'beat'" := (r 1).
(* end hide *)
(** printing und %\ensuremath{\wedge}% *)
(** printing oder %\ensuremath{\vee}% *)
(** printing impl %\ensuremath{\leadsto}% *)
(** printing farmer %\textsf{farmer}% *)
(** printing donkey %\textsf{donkey}% *)
(** printing laugh %\textsf{laugh}% *)
(** printing bray %\textsf{bray}% *)
(** printing own %\textsf{own}% *)
(** printing beat %\textsf{beat}% *)

(** To make terms more readable, I introduce familiar notation, as shown in figure %\ref{fig:notation}%.
%\begin{figure}\centering
$\begin{array}{|ll|ll|}\hline%
  [true] %& \textit{true} &% 
  [farmer] %& \textit{p} 0 \\%
  [false] %& \textit{false} &%
  [donkey] %& \textit{p} 1 \\%
  [not] %& \textit{not} &%
  [laugh] %& \textit{p} 2 \\%
  [and] %& \textit{and} &%
  [bray] %& \textit{p} 3 \\%
  [or] %& \textit{or} &%
  [own] %& \textit{r} 0 \\%
  [imply] %& \textit{imply} &%
  [beat] %& \textit{r} 1 \\\hline
 \end{array}$
\caption{Abbreviations for constants}
\label{fig:notation}
\end{figure}%
*)

Example Every_donkey_brayed : all (fun x => donkey x impl bray x) = all (fun x => (p 1 x) impl (p 3 x)).
Proof.
  reflexivity.
Qed.

(** The intended interpretation of terms of type [t] is of course in
an algebra (boolean or heyting) where [true] is understood as truth
(the top element of the algebra), and [false] as falsity (the bottom
element of the algebra).  The connective symbols are to be understood
as appropriate operations in the algebra (meet, join, and complement
if in a boolean algebra, and meet, join and relative complement in a
heyting algebra).  Although this setup is independent of one's
particular choice of logic (classical or intuitionistic), classical
logic is more familiar in linguistics, and generates a coarser
equivalence relation over terms.  I will write $\phi \equiv \psi$ to 
indicate that $\phi$ is classically equivalent to $\psi$. *)
(* begin hide *)
Inductive t_to_Prop (phi : t) : Prop :=
| t_to_Prop_constructor : t_to_Prop phi.
Fixpoint eval_phi phi : Prop :=
  match phi with
    | true => True
    | false => False
    | not psi => (eval_phi psi) -> False
    | psi und eta => (eval_phi psi) /\  (eval_phi eta)
    | psi oder eta => (eval_phi psi) \/ (eval_phi eta)
    | psi impl eta => (eval_phi psi) -> (eval_phi eta)
    | some P => (forall (a : e), ((eval_phi (P a)) -> False)) -> False 
    | all P => (forall (a : e), eval_phi (P a))
    | psi => t_to_Prop psi
   end.
Notation "phi 'equiv' psi" := (eval_phi phi <-> eval_phi psi) (at level 69).
(* end hide *)
(** printing equiv %\ensuremath{\mathrel{\equiv}}% *)
(** printing eta %\ensuremath{\eta}% *)
(** printing phi %\ensuremath{\phi}% *)
(** printing psi %\ensuremath{\psi}% *)
(** printing chi %\ensuremath{\chi}% *)
(* begin hide *)
Fixpoint repeat_type (n : nat) (i : Type) (o : Type) : Type :=
  match n with
    | O => o
    | S m => i -> repeat_type m i o
  end.
Notation "e ^^ n" := (repeat_type n e) (at level 30).
(* end hide *)
(** The notation [i^^n o] abbreviates the type
$\underbrace{i \rightarrow \cdots \rightarrow i}_{n\ times}
\rightarrow o$.  *)


(* begin hide *) 
Section dyn. 
(* end hide *)
(** * Dynamism *)

(** In this section, dynamism is introduced to the system
   above.  Although the dynamic properties of connectives are
   typically argued for based on the behaviour of pronouns, the
   statement of the dynamic properties of connectives needn't make
   reference to pronouns, which is exploited here.

   The intuitive understanding of the dynamic meaning of a sentence is
   as explicating its contribution to the discourse; it specifies how
   the meaning of the upcoming discourse is influenced by its own
   meaning.  Accordingly the dynamic type $\Omega$ of a sentence is [t ->
   t]; a function which modifies the meaning of an upcoming discourse.
   *)
(* begin hide *)
  Definition Omega := t -> t.
(* end hide *)
(** printing Omega %\ensuremath{\Omega}% *)
(** Dynamic translations of terms of type [t] into terms of type [Omega]
are now defined.  These terms of type [Omega] are intended to capture in
an intuitive way the _dynamic_ meaning of the original terms of type
[t].  *)

(** Atomic sentences, qua n-ary predicates, are simply conjoined with
the discourse continuation.  That is, the meaning of a discourse
consisting of only atomic sentences is hereby stipulated to be their
conjunction.  *)

Fixpoint atom_d_tr (n : nat) : (e^^n) t -> (e^^n) Omega :=
  match n with
  | O => fun atom phi => atom und phi
  | S m => fun atom x => atom_d_tr m (atom x)
  end.

Example dynamic_beats : atom_d_tr 2 beat = fun x y phi => beat x y und phi.
Proof.
  reflexivity.
Qed.

(** The atomic sentences [true] and [false], representing the always true and
always false sentences, obtain from the general treatment of atomic
sentences above the meanings [fun phi => true und phi] and [fun phi => false und phi]
respectively, which are semantically equivalent to the identity
function and the constant false function respectively.  To simplify
the statement of the main result, the translations of [true] and [false] are
simply taken to be these simpler functions.  *)

Definition true_d_tr : Omega := fun phi => phi.

Example true_id : forall phi, atom_d_tr O true phi equiv true_d_tr phi.
Proof.
  simpl; intuition.
Qed.

Definition false_d_tr : Omega := fun _ => false.

Example false_false : forall phi, atom_d_tr O false phi equiv false_d_tr phi.
Proof.
  simpl; intuition.
Qed.  

(** Connectives are classified as externally dynamic just in case a
discourse referent introduced internally to them is accessible
externally.  They are internally dynamic just in case a discourse
referent introduced inside of one conjunct is accessible in the other.

   As conjunction is externally dynamic, the discourse continuation of
   a conjunction should be in the scope of both conjuncts.  As it is
   also internally dynamic, the second conjunct should be in the scope
   of the first.  The discoure continuation of the first conjunct [P]
   is thus the result of continuing the second conjunct [Q] with the
   discourse continuation of the entire coordination, [phi].  In other
   words, a discourse [P und Q. D] is interpreted as [P. Q. D].*)

Definition and_d_tr : Omega -> Omega -> Omega :=
  fun (P Q : Omega) (phi : t) => P (Q phi).

(** Negation is externally static (i.e. not externally dynamic); so
   the discourse continuation of a negated expression [P] must not be
   in its scope.  Instead, the negated expression [P] is given a
   trivial discourse continuation, [true], and its negation is treated as
   an atomic proposition; i.e. it is conjoined with the remainder of
   the discourse.  *)

Definition not_d_tr : Omega -> Omega := 
  fun (P : Omega) => atom_d_tr 0 (not (P true)).

Example not_d_tr_externally_static :
  forall (P : Omega) (phi : t), not_d_tr P phi = not (P true) und phi.
Proof.
  reflexivity.
Qed.

(** The other dynamic connectives will be defined in terms of dynamic
conjunction and dynamic negation.  Dynamic behaviour, whether internal
or external, will implicate a dynamic conjunction, and static
behaviour a dynamic negation.


Implication is externally static, but internally dynamic from
   antecedent [P] to consequent [Q].  This is captured by its
   classically valid reformulation in terms of [and] and [not]: 
%\( P \rightarrow Q \equiv \neg (P \wedge \neg Q)\)% *) 

Definition imp_d_tr : Omega -> Omega -> Omega := 
  fun (P Q : Omega) => not_d_tr (and_d_tr P (not_d_tr Q)).

(** The dynamic behaviour of disjunction is less clear
%\citep{GroenendijkStokhof91}% .  Sentences like: "Either this house
doesn't have a bathroom, or it is hidden" suggest that disjunction
should be (at least) internally dynamic, however it is common to
assume that disjunction is in fact completely static.  This is in fact
predicted by its classical reformulation in terms of negation and
conjunction: %\( P \vee Q \equiv \neg (\neg P \wedge \neg Q)\)% *) 


Definition or_d_tr : Omega -> Omega -> Omega :=
  fun (P Q : Omega) => not_d_tr (and_d_tr (not_d_tr P) (not_d_tr Q)).

(** The generic treatment of dynamic GQs has it that the discourse
continuation of the entire sentence is moved into the scope of the
GQ. *)

Definition quant_d_tr (q : (e -> t) -> t) : (e -> Omega) -> Omega :=
  fun (P : e -> Omega) (phi : t) => q (fun x => P x phi).

(** Exceptionally, from this perspective, universal quantification is
externally static, which is captured by its de Morgan reformulation in
terms of existential quantification: %\( \forall x.P x \equiv \neg \exists x.\neg P x \)% *) 

Definition all_d_tr : (e -> Omega) -> Omega :=
  fun (P : e -> Omega) => not_d_tr (quant_d_tr some (fun x => not_d_tr (P x))).


(** These definitions allow for a concise statement of the translation
[d_tr] (mnemonic for _dynamic_ translation) from terms of type [t],
with their dynamic potential _implicit_ into terms of type [Omega] with
their dynamic meanings made _explicit_.  We see that the translation
[d_tr] is just a homomorphism. *)

Fixpoint d_tr (phi : t) : Omega :=
  match phi with
    | true => true_d_tr
    | false => false_d_tr
    | p n x => atom_d_tr 1 (p n) x
    | r n x y => atom_d_tr 2 (r n) x y
    | not psi => not_d_tr (d_tr psi)
    | psi und chi => and_d_tr (d_tr psi) (d_tr chi)
    | psi oder chi => or_d_tr (d_tr psi) (d_tr chi)
    | psi impl chi => imp_d_tr (d_tr psi) (d_tr chi)
    | pro P => quant_d_tr pro (fun x => d_tr (P x))
    | some P => quant_d_tr some (fun x => d_tr (P x))
    | all P => all_d_tr (fun x => d_tr (P x))
  end.

(** This translation, as can be seen by the examples to follow, allows
existentials to dynamically extend their scope over upcoming
sentences, while disallowing universals from doing the same. *)

Example Some_farmer_laughed : 
  forall phi : t,
  d_tr (some (fun x => farmer x und laugh x)) phi
  equiv some (fun x => farmer x und laugh x und phi).
Proof.
  simpl; intuition;
  repeat (match goal with
    | [ H : _ -> False |- _ ] => (apply H; clear H)
    | [ a : e, H : forall (a : e), _ -> False |- _ ] => apply (H a); clear H
  end; intuition).
Qed.

Example Every_farmer_laughed :
  forall phi : t, 
    d_tr (all (fun x => farmer x impl laugh x)) phi
  equiv (all (fun x : e => farmer x impl laugh x)) und phi.
Proof.
  simpl;
  intuition;
  match goal with
    | [ H : _ -> False |- _ ] => apply H
  end;
  intuition.
Qed.

(* begin hide *)
End dyn.
(* end hide *)


(* begin hide *)
Section contexts.
(* end hide *)

(** * Contexts *)



(** Here we present an interpretation of context-independent sentences
   into context _dependent_ ones.  This does not presuppose (or
   introduce) dynamism.

   Following %\citet{DeGroote06}%, we introduce a new type $\gamma$
   for contexts.  *)
(* begin hide *)
Variable gamma : Set.
(* end hide *)
(** printing gamma %\ensuremath{\gamma}% *)
(** This type is _abstract_, in the sense that its properties will be
given axiomatically; _anything_ that satisfies these properties may be
used as a context.  We require only that we can interact with objects
of type [gamma] in two ways.  First, that a context may be updated
with an individual to obtain a new context.  *)

Variable update : e -> gamma -> gamma.

(** The notation $x\mathrel{\hbox{\tt ::}}c$ will abbreviate the more cumbersome [update x c].*)
(* begin hide *)
Notation "x 'upd' l" := (update x l) (at level 45).
(* end hide *)
(** printing upd %\ensuremath{\mathrel{\hbox{\tt ::}}}% *)

(** And second, that salient individuals may be retrieved from a
context. *)

Variable sel : gamma -> e.

(** In particular, [sel] should be thought of as a placeholder for
   one's favourite pronoun resolution algorithm; in this view, the job
   of semantics is to give the appropriate input to the pronoun
   resolution algorithm, but the inner workings of this algorithm are
   semantically opaque.  %\citet{DeGroote06}% takes for concreteness
   [gamma] to be the type of lists of individuals, updating to be
   achieved by adding an individual to a list, and selection to be
   retrieving some element of a list.  *)

(** Terms of type [t] will be viewed as having implicit contexts.  We
will define a translation from terms of type [t] which makes their
contexts, context updating, and context passing explicit.  *)

(** Contexts are incorporated by adding a context parameter to every
atomic type.  *)

Definition G := gamma -> t.

Definition E := gamma -> e.

(** Thus a term of type [t] will be translated into one of type [G],
and one of type [e] will be translated into one of type [E]. *)


(** Inherently context insenstitive [n]-ary connectives, functions,
   and predicates can be lifted to context sensitive ones by simply
   distributing the context to their context-sensitive arguments.  *)

Fixpoint distr_g_tr {A B : Type} (n : nat) : (gamma -> (A ^^ n) B) -> ((gamma -> A) ^^ n) (gamma -> B) :=
  match n as n0 return (gamma -> (A ^^ n0) B) -> ((gamma -> A) ^^ n0) (gamma -> B) with
  | O => fun xx => xx
  | S m => fun xx phi => distr_g_tr m (fun c : gamma => xx c (phi c))
  end.

Definition lift_g_tr {A B : Type} (n : nat) (m : (A ^^ n) B) : ((gamma -> A) ^^ n) (gamma -> B) :=
  @distr_g_tr A B n (fun _ => m).

Example contextual_individual (j : e) : lift_g_tr (A := e) 0 j = (fun _ => j).
Proof.
  reflexivity.
Qed.

Example contextual_beats : lift_g_tr 2 beat = fun x y c => beat (x c) (y c).
Proof.
  reflexivity.
Qed.

(** A pronoun [pro] is translated as a generalized quantifier
generated from the (context-sensitive) individual [sel].  *)

Definition pro_g_tr : (E -> G) -> G := fun P => P sel.

(** The individual argument to the property of a GQ is a lifted
   context-insensitive variable.  The context passed to this property
   is enriched with the unlifted variable.  *)

Definition quant_g_tr (gq : (e -> t) -> t) : (E -> G) -> G :=
  fun P (c : gamma) => gq (fun x => P (lift_g_tr (A := e) 0 x) (x upd c)).

(** The function [g_tr] (mnemonic for _gamma_ translation) makes
explicit the implicit context manipulation in terms of type [t]. *)

Fixpoint g_tr (phi : t) : G :=
  match phi with
    | true => lift_g_tr (A := t) 0 true
    | false => lift_g_tr (A := t) 0 false
    | not psi => lift_g_tr 1 not (g_tr psi)
    | psi und chi => lift_g_tr 2 and (g_tr psi) (g_tr chi)
    | psi impl chi => lift_g_tr 2 imply (g_tr psi) (g_tr chi)
    | psi oder chi => lift_g_tr 2 or (g_tr psi) (g_tr chi)
    | p n a => lift_g_tr 1 (p n) (lift_g_tr (A := e) 0 a)
    | r n a b => lift_g_tr 2 (r n) (lift_g_tr (A := e) 0 a) (lift_g_tr (A := e) 0 b)
    | some P => quant_g_tr some (fun (x : E) (c : gamma) => g_tr (P (x c)) c)
    | all P => quant_g_tr all (fun (x : E) (c : gamma) => g_tr (P (x c)) c)
    | pro P => pro_g_tr (fun (x : E) (c : gamma) => g_tr (P (x c)) c) 
  end.


(** In the example below, which is the translation of the sentence _he
laughed_ into context-sensitive terms, note that the referent of the
pronoun _he_ must be found in the context of utterance [c]. *)

Example he_laughed : 
  forall (c : gamma), g_tr (pro laugh) c = laugh (sel c).
Proof.
  reflexivity.
Qed.  

(** In the following example, the translation of the sentence _some
farmer owned it_, note that the referent of _it_ is to be found in the
context of utterance [c] which has been updated with a discourse
referent [x] which is a farmer.  Of course, for multiple reasons (the
pronoun is incompatible with the animacy of the farmer, and the
pronoun is syntactically too local) the pronoun should not in this
case be resolved to the discourse referent [x]. *)

Example some_farmer_owned_it : 
  forall (c : gamma), g_tr (some (fun x => farmer x und (pro (fun y => own y x)))) c
                  = some (fun x : e => farmer x und own (sel (x upd c)) x).
Proof.
  reflexivity.
Qed.

(* begin hide *)
End contexts.
(* end hide *)

(* begin hide *)
Section deGroote.
(* end hide *)
(** * De Groote's Montagovian Dynamics *)


(* Next I recall %\citeauthor{deGroote}%'s dynamic approach with
   contexts, which I show in a later theorem to be equivalent to the
   composition of [g_tr] with [d_tr] *)
(* begin hide *)
Variable gamma : Set.
Variable update : e -> gamma -> gamma.
Variable sel : gamma -> e.
Notation "x 'upd' l" := (update x l) (at level 60, right associativity).
(* end hide *)
(** printing upd %\ensuremath{\mathrel{\hbox{\tt ::}}}% *)

(** The type of a sentence $\omega$ is defined to be [gamma -> (gamma -> t) -> t]; a function from a context [gamma] to the type [(gamma -> t) -> t] of the _continuation_ of a context.
 *)
(* begin hide *)
Definition oomega := gamma -> (gamma -> t) -> t.
(* end hide *)
(** printing oomega %\ensuremath{\omega}% *)

(** Atomic predicates do not modify their context; they simply conjoin
    their static meaning with the meaning of the discourse
    continuation in the context.*)

Definition pred_dg_tr (n : nat) : e -> oomega :=
  fun (x : e) (c : gamma) (phi : gamma -> t) => (p n x) und (phi c).

Definition rel_dg_tr (n : nat) : e -> e -> oomega :=
  fun (x y : e) (c : gamma) (phi : gamma -> t) => (r n x y) und (phi c).

(** %\citeauthor{DeGroote06}% treats verbs as taking generalized
quantifiers as arguments, as opposed to individuals (in contrast to
nouns).  This decision is orthogonal to the question of interest here,
and requires a richer setup than present in his
%\citeyear{DeGroote06}% paper to treat the composition of semantic
translations. *)

(** While %\citet{DeGroote06}% does not deal explicitly with
sentential connectives, his later work (as described by
%\citet{LebedevaPhD}%) does, and is as follows. *)

Definition and_dg_tr : oomega -> oomega -> oomega :=
  fun (P Q : oomega) (c : gamma) (phi : gamma -> t) => P c (fun d => Q d phi).

Definition not_dg_tr : oomega -> oomega :=
  fun (P : oomega) (c : gamma) (phi : gamma -> t) => (not (P c (fun _ => true))) und (phi c).

Definition or_dg_tr : oomega -> oomega -> oomega :=
  fun (P Q : oomega) => not_dg_tr (and_dg_tr (not_dg_tr P) (not_dg_tr Q)).

Definition imply_dg_tr : oomega -> oomega -> oomega :=
  fun (P Q : oomega) => not_dg_tr (and_dg_tr P (not_dg_tr Q)).

Definition some_dg_tr : (e -> oomega) -> oomega :=
  fun (P : e -> oomega) (c : gamma) (phi : gamma -> t) => some (fun (x : e) => P x (x upd c) phi).

Definition every_dg_tr : (e -> oomega) -> oomega :=
  fun (P : e -> oomega) => not_dg_tr (some_dg_tr (fun x => not_dg_tr (P x))).

Definition pro_dg_tr : (e -> oomega) -> oomega :=
  fun (P : e -> oomega) (c : gamma) (phi : gamma -> t) => P (sel c) c phi.

(** The function [dg_tr] (short for `De Groote' translation), makes
the implicit dynamism and context manipulation in terms explicit.*)

Fixpoint dg_tr (f : t) : oomega :=
  match f with
    | true => fun c phi => phi c
    | false => fun _ _ => false
    | P und Q => and_dg_tr (dg_tr P) (dg_tr Q)
    | P oder Q => or_dg_tr (dg_tr P) (dg_tr Q)
    | P impl Q => imply_dg_tr (dg_tr P) (dg_tr Q)
    | not P => not_dg_tr (dg_tr P)
    | some P => some_dg_tr (fun x => dg_tr (P x))
    | all P => every_dg_tr (fun x => dg_tr (P x))
    | p n x => pred_dg_tr n x
    | r n x y => rel_dg_tr n x y
    | pro P => pro_dg_tr (fun x => dg_tr (P x))
  end.

Example if_a_farmer_owns_a_donkey_he_beats_it : forall c phi, 
   dg_tr ((some (fun x => farmer x und some (fun y => donkey y und own y x))) impl pro (fun u => pro (fun v => beat v u))) c phi 
         equiv
   ((all (fun x : e => farmer x impl 
                     all (fun y : e => (donkey y und own y x) impl 
                                     beat (sel (y upd x upd c)) (sel (y upd x upd c)))))
      und phi c).
Proof.
  simpl; intuition.
  repeat (match goal with
    | [ H : _ -> False |- _ ] => apply H
  end;
  intuition).
Qed.

(* begin hide *)
End deGroote.
(* end hide *)


(* begin hide *)
Section deGroote_equiv_g_d.
(* end hide *)
(** * The equivalence *)

(** The translations must be restricted so as to use the same type [gamma] and same accessor functions [update] and [sel]. *)

(* begin hide *)
Variable gamma : Set.

Variable update : e -> gamma -> gamma.

Variable sel : gamma -> e.
Notation "x 'upd' l" := (update x l) (at level 60).
(* end hide *)
(** printing upd %\ensuremath{\mathrel{\hbox{\tt ::}}}% *)

Definition g_trans := g_tr gamma update sel.

Definition dg_trans := dg_tr gamma update sel.

(** In order to prove the equivalence between de Groote's translation
and the composition of the gamma and dynamic translations, I assume
that functions are extensional; that two functions are identical iff
they compute the same input-output relation. *)

Hypothesis fun_ext : forall (A B : Set) (f g : A -> B), (forall x, f x = g x) -> f = g.

(* begin hide *)
Hint Resolve fun_ext : dG_d_g.
Lemma add_some : forall (P Q : e -> t), P = Q -> some P = some Q.
Proof.
  intros; subst; reflexivity.
Qed.
Hint Resolve add_some : dG_d_g.
Lemma add_and : forall phi phi' chi chi', phi = phi' -> chi = chi' -> and phi chi = and phi' chi'.
Proof.
  intros; subst; reflexivity.
Qed.
Hint Resolve add_and : dG_d_g.
Lemma add_not : forall phi phi', phi = phi' -> not phi = not phi'.
Proof.
  intros; subst; reflexivity.
Qed.
Hint Resolve add_not : dG_d_g.
Ltac rewriteEq1 :=
  match goal with
    | [ H : forall _, _ = _ |- _ ] => rewrite H
  end.
Hint Extern 3 => rewriteEq1 : dG_d_g.
Ltac rewriteEq2 :=
  match goal with
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H
  end.
Hint Extern 3 => rewriteEq2 : dG_d_g.
Ltac unfoldAll :=
  simpl; unfold atom_d_tr, distr_g_tr, lift_g_tr, quant_g_tr, some_dg_tr, not_d_tr,
         not_dg_tr, imply_dg_tr, every_dg_tr, and_d_tr,
         and_dg_tr, pro_dg_tr, pro_g_tr, or_dg_tr, or_d_tr; 
  simpl; unfold atom_d_tr, distr_g_tr,
         quant_g_tr, some_dg_tr, not_d_tr,
         not_dg_tr, imply_dg_tr, every_dg_tr, and_d_tr,
         and_dg_tr, pro_dg_tr, pro_g_tr, or_dg_tr, or_d_tr.
Hint Extern 1 => unfoldAll : dG_d_g.
Ltac applyFunExt := apply fun_ext; intro.
Hint Extern 3 => applyFunExt : dG_d_g.

(* end hide *)


(** The main theorem states that, for any formula [phi] of type [t],
the context-change poential of the contextification of its dynamic
translation is identical to the context-change potential of de
Groote's translation of it.  
*)

Theorem dg_g_d : 
  forall (phi psi : t), g_trans ((d_tr phi) psi)  = fun c => (dg_trans phi) c (g_trans psi).
(** %\begin{proof}% This is proven by induction on [phi], followed by simple but tedious case analysis. %\end{proof}%*)
Proof.
  induction phi;
  auto 8 with dG_d_g.
Qed.

(** One peculiarity about the statement of the theorem concerns the
function [g_trans] on the right hand side of the equation.  This is
because the discourse context desired on the left hand side ([psi]) is
of type [t], whereas that desired on the right ([g_trans psi]) is of
type [gamma -> t].  In order for the theorem to make sense, both sides
must be given the same discourse continuation.  The term [g_trans] on
the right of the equation coerces a term of type [t] into one of type
[gamma -> t].  In essence, the theorem says only that [g_trans] composed
with [d_tr] has the same effect on a discourse configuration of type
[t] that [dg_trans] has on its image under [g_trans].

In practice, this is not much of a restriction, as for any discourse
[phi], the theorem implies that both left and right sides are
interpreted identically in the empty discourse continuation. *)

Corollary dg_g_d_true : 
  forall (phi : t), g_trans (d_tr phi true) = fun c => dg_trans phi c (fun _ => true).
Proof.
  intros phi;
  rewrite (dg_g_d phi);
  reflexivity.
Qed.
  
(* begin hide *)
End deGroote_equiv_g_d.
(* end hide *)

(* begin hide *)
End obj.
(* end hide *)

(** * Conclusion

The simple perspective offered by %\citet{DeGroote06}% on dynamism and
dynamic updating has been shown to be decomposible into two simpler
and logically independent parts.  His %\citeyear{DeGroote06}% system,
modeled here, involves an mapping of _second-order_ terms in a source
language into those in a target language.  This amounts to a
tree-to-term homomorphism, and allows %\citeauthor{DeGroote06}% to
avoid defining %\(\lambda\)%-homomorphisms.  This has been improved
upon in later work %\citep{LebedevaPhD}%, where the source language is
made higher order.  In order to have a simple statement of the two
parts that De Groote's system can be factored into (dynamism and
context-sensitivity), I have departed from his original presentation
in some ways.  In particular, I have presented the source and target
languages as one and the same, whereas %\citeauthor{DeGroote06}%
treats the source language as properly syntactic, and the target
language as properly semantic.  Collapsing source and target languages
has the aesthetically unpleasant consequence of introducing a
%`%meaningless%'% term, [pro], into the language.  While the same
could have been done with the term %\textbf{who}%, I have chosen to
leave it out of the language altogether, as it plays no illustrative
semantic role.  The second difference concerns the type of verbal
elements in the source language, where, for %\citeauthor{DeGroote06}%,
they take generalized quantifier denoting expressions as arguments:
%\(\den{\texttt{beat}} := \lambda X,Y.X(\lambda x.Y(\lambda
y.%[beat]%\ x\ y))\)%.  This is made very simple in his presentation
by treating %\texttt{beat}% as a constant in a language different from
that of [beat].  This is not available to me, as both [g_tr] and
[d_tr] should be defined independently of each other, and therefore
must operate on the same source language, whence at least [d_tr] must
map one language to itself.  While this is a salient theoretical
decision regarding the proper treatment of quantifier scope, it does
not matter for the decomposition of %\citeauthor{DeGroote06}%'s
translation into the two simpler ones given here.

*)
