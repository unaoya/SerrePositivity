module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluationAll
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebra

/-!
模型。文献の定義との比較は後で
# Schur 代数からの評価と生成元の射の持ち上げ

概要：Berger–Moerdijk §1 の全合成の評価式から、評価射と生成元の持ち上げを代数射として構成する。
方針：評価射の全 arity の作用保存を使い、持ち上げを Schur 関手の射と評価の合成で与える。
規約：始域の代数は既存の Schur 作用を持つ freeAlgebra。
使われ方：自由・忘却随伴の Hom 対応の逆写像と余単位を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：Schur 対象から任意の代数への評価は代数射である（Berger–Moerdijk §1）。
方針：底の複体射に既存の評価を使い、全合成の評価から作用保存を得る。
規約：零入力の作用も保存する。
使われ方：自由・忘却随伴の余単位の成分となる。 -/
def evaluationHom (X : P.Algebra) : P.freeAlgebra X.carrier ⟶ X where
  hom := X.evaluation
  comm n := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebra]
    rw [id_tensorHom]
    exact X.evaluation_action n

/-- 概要：評価代数射の底の複体射は Schur 評価である（Berger–Moerdijk §1）。
方針：評価代数射の定義を評価する。
規約：忘却後の射の等式。
使われ方：余単位の自然性を既存の評価の自然性から導く。 -/
@[simp]
lemma evaluationHom_hom (X : P.Algebra) : X.evaluationHom.hom = X.evaluation := rfl

/-- 概要：生成元の複体射を Schur 代数からの代数射へ持ち上げる（Berger–Moerdijk §1）。
方針：自由代数関手による射と標的代数の評価代数射を合成する。
規約：持ち上げの底の射は既存の schurLift と一致する。
使われ方：自由・忘却随伴の Hom 対応の逆方向を構成する。 -/
def liftHom {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) :
    P.freeAlgebra K ⟶ X :=
  P.freeAlgebraFunctor.map f ≫ X.evaluationHom

/-- 概要：生成元の持ち上げの底の射は Schur 持ち上げである（Berger–Moerdijk §1）。
方針：関手の射と代数射の合成の定義を評価する。
規約：底の射は chain map の等式として比較する。
使われ方：持ち上げの生成元上の値と自然性を既存の Schur 持ち上げから導く。 -/
@[simp]
lemma liftHom_hom {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) :
    (X.liftHom f).hom = X.schurLift f := rfl

/-- 概要：持ち上げ代数射は指定した生成元の射を延長する（Berger–Moerdijk §1）。
方針：底の射を Schur 持ち上げへ戻し、生成元上の評価を使う。
規約：生成元の包含は既存の schurUnit。
使われ方：自由・忘却随伴の Hom 対応の一方の逆律となる。 -/
@[reassoc]
lemma schurUnit_liftHom {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) :
    P.schurUnit K ≫ (X.liftHom f).hom = f :=
  X.schurUnit_schurLift f

/-- 概要：持ち上げ代数射は生成元への前合成と両立する（Berger–Moerdijk §1）。
方針：代数射を底の射で比較し、Schur 持ち上げの前合成の式を使う。
規約：標的の代数を固定する。
使われ方：自由・忘却随伴の Hom 対応の始域に関する自然性を与える。 -/
lemma liftHom_precomp {K L : Complex A} (X : P.Algebra) (h : K ⟶ L) (f : L ⟶ X.carrier) :
    P.freeAlgebraFunctor.map h ≫ X.liftHom f = X.liftHom (h ≫ f) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  exact X.schurLift_precomp h f

/-- 概要：持ち上げ代数射は標的の代数射との後合成と両立する（Berger–Moerdijk §1）。
方針：底の射へ帰着し、Schur 持ち上げの後合成の式を使う。
規約：後合成の射は全 arity の作用を保つ。
使われ方：自由・忘却随伴の Hom 対応の終域に関する自然性を与える。 -/
lemma liftHom_postcomp {K : Complex A} {X Y : P.Algebra}
    (f : K ⟶ X.carrier) (g : X ⟶ Y) :
    X.liftHom f ≫ g = Y.liftHom (f ≫ g.hom) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift_postcomp f g

/-- 概要：Schur 代数からの評価代数射は代数に関する自然変換をなす（Berger–Moerdijk §1）。
方針：底の評価の自然性を代数射の等式へ移す。
規約：忘却してから自由代数関手を適用した関手を始域とする。
使われ方：自由・忘却随伴の余単位となる自然変換を構成する。 -/
def evaluationAlgebraNatTrans (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P ⋙ P.freeAlgebraFunctor ⟶ 𝟭 P.Algebra where
  app X := X.evaluationHom
  naturality {_X _Y} f := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.evaluation_naturality f).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
