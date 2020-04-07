\documentclass{scrartcl}

\usepackage[english]{babel}

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{mathtools}
\usepackage[mathscr]{eucal}
\usepackage[linkcolor=darkred,colorlinks,pdfpagelabels]{hyperref}
\usepackage{color}
\usepackage{fontspec}
\setsansfont{STIX2Math.otf} % not a sans serif font but contains most characters
\usepackage{agda}

\definecolor{darkred}{rgb}{0.5,0,0}

\theoremstyle{definition}
\newtheorem{Def}{Definition}

\theoremstyle{plain}
\newtheorem{Lma}{Lemma}
\newtheorem{Prp}{proposition}
\newtheorem{Thm}{Theorem}
\newtheorem{Cor}{Corollary}

\theoremstyle{remark}
\newtheorem{Rem}{Remark}

\newcommand{\N}{\ensuremath{\mathbb{N}}}
\newcommand{\Z}{\ensuremath{\mathbb{Z}}}
\newcommand{\Q}{\ensuremath{\mathbb{Q}}}
\newcommand{\R}{\ensuremath{\mathbb{R}}}
\renewcommand{\L}{\ensuremath{\mathscr{L}}}
\newcommand{\ZFC}{\ensuremath{\mathrm{ZFC}}}
\newcommand{\limp}{\rightarrow}
\newcommand{\liff}{\leftrightarrow}
\newcommand{\Pow}{\mathcal{P}}
\newcommand{\sep}{\,|\,}
\newcommand{\eqdef}{:=}
\newcommand{\quot}[2]{#1/\!\!#2}

\DeclareMathOperator{\Rel}{Rel}
\DeclareMathOperator{\Ind}{Ind}
\DeclareMathOperator{\Trans}{Trans}
\DeclareMathOperator{\Ord}{Ord}
\DeclareMathOperator{\Eq}{Eq}

\theoremstyle{plain}
\newtheorem{Exc}{Exercise}

\begin{document}

\begin{code}[hide]
  open import Agda.Primitive
  open import Agda.Builtin.Equality
  import Agda.Builtin.Sigma as Sigma

  infixr 2 _×_

  Σ : {ℓ ℓ' : Level} → {A : Set ℓ} → (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Σ = Sigma.Σ _

  _×_ : {ℓ ℓ' : Level} → (A : Set ℓ) → (B : Set ℓ') → Set (ℓ ⊔ ℓ')
  A × B = Sigma.Σ A λ _ → B
\end{code}

These exercises are meant to accompany the talk 2018--02--08 at the Initial Types Club of Chalmers university of technology and Gothenburg university. They mostly constitute, and are meant to illustrate, basic facts of $\ZFC$ which are principally taken from the books \cite{moschovakis:2006} and \cite{jech:2002} also referred to in the notes of the talk. As such solutions may almost always be found in the notes or their references.

\begin{Exc}[Cartesian products\label{exc:prod}]
  Using the Kuratowski pairing operation
  \begin{align*}
    [x = (y,z)] \eqdef [x = \{\{y\},\{y,z\}\}]
  \end{align*}
  construct a class function $[x = A \times B]$ and verify the following:
  \begin{enumerate}
  \item $[x = (y,z)]$ is a class function in $\ZFC$.
  \item $[x = A \times B]$ is a class function in $\ZFC$.
  \item $\ZFC \vdash \forall x, y, u, v ((x,y) = (u,v) \limp x = u \land y = v)$.\label{exc:prod.3}
  \item $\ZFC \vdash \forall A, B, p (p \in A \times B \liff \exists x \in A, y \in B (p = (x,y)))$.\label{exc:prod.4}
  \end{enumerate}
  Hint: to construct $A \times B$, first find a set containing all pairs from it and use separation.
\end{Exc}

\begin{Exc}[Relations and functions\label{exc:rel}]
  In $\ZFC$ we identify relations and functions with their graphs, i.e.~subsets of the Cartesian product. A consequence is that the equalities between relations and functions, respectively, are extensional. With a pairing operation which satisfies \ref{exc:prod.3} and \ref{exc:prod.4} from the previous exercise:
  \begin{enumerate}
  \item Construct a formula $\Eq(r,A)$ saying that $r \subset A \times A$ is an equivalence relation on $A$.
  \item Construct a formula $f : A \longrightarrow B$ saying that $f$ is a function from $A$ to $B$.
  \item Construct a class function $[x = {}^AB]$ such that $\ZFC \vdash \forall A, B \forall f (f \in {}^AB \liff f : A \longrightarrow B)$.
  \item Assuming we have a set $\N = (N,0,S)$ of natural numbers (see Exercise \ref{exc:nat}), verify that the axiom of foundation is equivalent to the sentence
    \begin{align*}
      \neg \exists A \exists f : N \longrightarrow A \forall n \in N (f(S(n)) \in f(n))
    \end{align*}
    relative to the other axioms of $\ZFC$.% Hint: Consider the range of $f$.
  \end{enumerate}
\end{Exc}

\begin{Exc}[Quotients\label{exc:quotients}]
  One important feature of $\ZFC$ is the ease with which it handles quotient sets. Construct a class-function $[x = \quot{A}{\sim}]$ and prove
  \begin{align*}
    \ZFC \vdash &\forall A, \sim (\Eq(\sim,A) \limp (\forall x \in \quot{A}{\sim} (x \not= \varnothing) \land\\
                &\quad \left(\bigcup \quot{A}{\sim}\right) = A \land \forall x,y \in \quot{A}{\sim} (x \not= y \limp x \cap y = \varnothing)\\
                &\quad \land \forall a,b \in A (a \sim b \liff \exists x \in \quot{A}{\sim} (a \in x \land b \in x)))\mbox{.}
  \end{align*}
  Thus for a set $A$ and an equivalence relation $\sim$ on $A$, the set $\quot{A}{\sim}$ is the quotient of $A$ by $\sim$, and its members are the equivalence classes of the elements of $A$. Note that as a consequence the equality on $\quot{A}{\sim}$ is the ordinary equality.
\end{Exc}

\begin{Exc}[Ordinals\label{exc:ord}]
  A central notion in classical set theory is that of ordinal (number). An ordinal is a specific representative of an ``isomorphism class'' of well-ordered sets. They are defined as follows: Let
  \begin{align*}
    \Trans(x) \eqdef \forall y \in x \forall z \in y (z \in x)\mbox{,}
  \end{align*}
  and
  \begin{align*}
    \Ord(\alpha) \eqdef \Trans(\alpha) \land \forall x, y \in \alpha (x \not\in x \land (x \in y \lor y \in x \lor x = y))\\
    \qquad \land \forall A \in \Pow(\alpha) (A \not= \varnothing \limp \exists x \in A \forall y \in A (x \in y \lor x = y))\text{.}
  \end{align*}
  Thus, an ordinal $\alpha$ is a transitive set well-ordered by (the restriction of) $\in$ (to $\alpha$).
  \begin{enumerate}
  \item Verify that the empty set is an ordinal.
  \item Show that every element of an ordinal is an ordinal.
  \item Show that, if $\alpha \subset \beta$ are ordinals, then $\alpha \in \beta$. Hint: consider $\beta \setminus \alpha = \{x \in \beta \sep x \not\in \alpha\}$.
  \item Show that if $\alpha$ and $\beta$ are ordinals, then $\alpha \subseteq \beta$ or $\beta \subseteq \alpha$. Use the above to conclude that $\alpha \in \beta$ or $\beta \in \alpha$ or $\alpha = \beta$. Hint: consider $\alpha \cap \beta$.
  \item Let $\varphi(x,\bar{p})$ be a formula with the shown free variables. Show that for all $\bar{p}$, if $\varphi(x,\bar{p})$ holds for at least one $x$ and only if $x$ is an ordinal, then there is an ordinal $\alpha$ such that $\varphi(\alpha,\bar{p})$ and for all ordinals $\beta$ with $\varphi(\beta,\bar{p})$ do we have $\alpha \subseteq \beta$. Conclude that the ordinals are ``well-ordered'' by $\in$. Hint: define $\alpha$ to satisfy the last requirement and verify the first.
  \item Show that, for each ordinal $\alpha$, $\alpha \cup \{\alpha\}$ is an ordinal and the successor of $\alpha$ in the order from the previous exercise ($\alpha \cup \{\alpha\}$ is then called a successor ordinal).
  \item Show that if $\alpha$ is an ordinal which is not a successor ordinal, then $\alpha = \bigcup \alpha (= \bigcup_{\beta \in \alpha} \beta)$ ($\alpha$ is then called a limit ordinal).
  \item Show that for each well-ordered set there is a unique ordinal isomorphic to it. Hint: uses replacement.
  \end{enumerate}
\end{Exc}

\begin{Exc}[Natural numbers\label{exc:nat}]
  The natural numbers consists of a triple $(N,0,S)$ satisfying the Peano axioms:
  \begin{align*}
    &0 \in N\mbox{,}\\
    &S : N \longrightarrow N\mbox{,}\\
    &\forall x, y \in N (S(x) = S(y) \rightarrow x = y)\mbox{,}\\
    &\forall x \in N (S(x) \not= 0)\mbox{,}\\
    &\forall A \in \Pow(N) (0 \in A \land \forall x \in A (S(x) \in A) \limp A = N)\mbox{.}
  \end{align*}
  In $\ZFC$ one often takes as $(N,0,S)$ above the triple $(\omega,\varnothing,\_^+)$, where $\omega$ is the smallest nonzero (i.e.~nonempty) limit ordinal, which can be defined by the (constant) class-function
  \begin{align}
    [x = \omega] \eqdef \forall z (z \in x \liff \forall A (\Ind(A) \limp z \in A))\text{.}\label{eq:omega}
  \end{align}
  and $[x = \alpha^+] \eqdef \alpha \cup \{\alpha\}$ is the ordinal successor class-function.
  \begin{enumerate}
  \item Show that $\omega$ is the least nonzero limit ordinal and that $(\omega,\varnothing,\_^+)$ satisfies the Peano axioms, for example in the following way:
    \begin{enumerate}
    \item Show that this is a class function (that is, $\omega$ exists and is unique with the property in \eqref{eq:omega}).
    \item Show that $\omega$ is inductive. Conclude that $\omega$ is nonempty and that the first, second and forth Peano axioms hold for $(\omega,\varnothing,\_^+)$.
    \item Verify the induction axiom for $(\omega,\varnothing,\_^+)$.
    \item Show by induction that $\omega$ is transitive.
    \item Show by induction that every element of $\omega$ is an ordinal.
    \item Use the properties from Exercise \ref{exc:ord} to conclude that $\omega$ is an ordinal, and the least nonzero limit ordinal.
    \item Use the properties from Exercise \ref{exc:ord} (or the foundation axiom) to verify the third Peano axiom for $(\omega,\varnothing,\_^+)$.
    \end{enumerate}
  \item Having verified there is a natural choice for a triple satisfying the Peano axioms, let $\N = (N,0,S)$ be any such triple. Verify that functions on $N$ can be defined by recursion in the sense that if $A$ is a set, $a \in A$ and $g : A \longrightarrow A$, then there is a unique $f : N \longrightarrow A$ such that
    \begin{align*}
      f(0) = a
      \qquad \text{and} \qquad
      f(S(n)) = g(f(n))
    \end{align*}
    for all $n \in N$. Construct $f$ as follows:
    \begin{enumerate}
    \item Let
      \begin{align*}
        D &= \{d \in \Pow(N) \sep 0 \in\ d \land \forall n \in N (S(n) \in d \limp n \in d)\}\text{ and}\\
        F &= \{p \in \Pow(N \times A) \sep \exists d \in D (p : d \longrightarrow A \land p(0) = a \land p(S(n)) = g(p(n)))\}\mbox{.}
      \end{align*}
      Show that, given $d,e \in D$ and $p,q \in F$ with $p : d \longrightarrow A$ and $q : e \longrightarrow A$, for all $n \in N$, we have $n \in d \cap e$ only if $p(n) = q(n)$.
    \item Verify that $\bigcup F$ is a function from $N$ to $A$ which satisfies the recursive equations and that it is unique with this property.
    \end{enumerate}
  \item Use recursion to show that any two triples satisfying the Peano axioms are uniquely isomorphic.
  \end{enumerate}
\end{Exc}
\pagebreak
\begin{Exc}[Implementation of constructive sets in Agda\footnote{Andreas, \cite{aczel:1978}}]
  A constructive notion of set can be implemented in Agda in the following way:
  \begin{code}
  data cset : Set₁ where
    node : (I : Set) → (f : I → cset) → cset
  \end{code}
  where the intuition is that \AgdaBound{I} is an index set and \AgdaBound{f} a function enumerating the constructive set, possibly with repetitions. Define equality, elementhood and subsethood as functions
  \begin{code}
  _∼_ : cset → cset → Set₀
  _∈_ : cset → cset → Set₀
  _⊆_ : cset → cset → Set₀
  \end{code}
  \begin{code}[hide]
  x ∼ y        = {!!}
  x ∈ node I f = {!!}
  x ⊆ y        = {!!}
  \end{code}
  in Agda. Hint: these will have to be defined mutually.
\end{Exc}

\bibliographystyle{plain}
\bibliography{Bibliography}

\end{document}
