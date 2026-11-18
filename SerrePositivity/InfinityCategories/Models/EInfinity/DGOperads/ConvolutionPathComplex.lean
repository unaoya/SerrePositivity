module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraInterval
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-!
模型。文献の定義との比較は後で
# 余代数区間に付随する複体の prepath object

概要：Berger–Moerdijk 命題 4.1、Berger–Fresse §3.1 の Hom(H,B) の底の複体を作る。
方針：区間の収縮と端点への前合成から定数射と評価射を構成する。
規約：この段では prepath object の三角形を証明し、代数構造とモデル的性質は後続で扱う。
使われ方：convolution の演算を備える functorial path object の底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A}

/-- 概要：区間から B への内部 Hom（BM 命題 4.1、BF §3.1）。
方針：既存の非有界線形 Hom 複体を用いる。
規約：全整数次数を含む。
使われ方：convolution の path object の底の複体となる。 -/
abbrev pathComplex (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) : Complex A :=
  homComplex A I.coalgebra.carrier B

/-- 概要：区間の収縮から定数関数への chain map（BF §3.1）。
方針：Hom(単位,B) と B の比較の後で収縮を前合成する。
規約：定数射は複体の射として構成する。
使われ方：path object の分解の第一射となる。 -/
def constant (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) : B ⟶ I.pathComplex B :=
  (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).inv ≫ homPrecompose I.contraction B

/-- 概要：区間の指定端点での評価射（BF §3.1）。
方針：端点を前合成し、Hom(単位,B) を B へ比較する。
規約：false と true の二端点を同じ定義で扱う。
使われ方：path object の二つの射影となる。 -/
def evaluation (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) (b : Bool) :
    I.pathComplex B ⟶ B :=
  homPrecompose (I.endpoint b) B ≫ (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom

/-- 概要：定数関数の端点評価は元の値となる（BF §3.1）。
方針：Hom の前合成の合成則と区間の端点・収縮の三角形を使う。
規約：全複体の chain map の等式である。
使われ方：prepath object の三角形の公理を満たす。 -/
lemma constant_evaluation (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) (b : Bool) :
    I.constant B ≫ I.evaluation B b = 𝟙 B := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.constant, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.evaluation, Category.assoc]
  rw [← homPrecompose_comp_assoc, I.endpoint_contraction]
  rw [← complexHomWhiskerRight, eHomWhiskerRight_id]
  change (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).inv ≫ 𝟙 _ ≫
    (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom = 𝟙 B
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- 概要：区間に付随する底の複体の prepath object（BM 命題 4.1）。
方針：Hom(H,B) と定数射・両端点評価を束ねる。
規約：モデル的な良さと P 代数構造はこの定義の仮定に含めない。
使われ方：代数としての functorial path object の底のデータを固定する。 -/
def prepathComplex (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) :
    HomotopicalAlgebra.PrepathObject B where
  P := I.pathComplex B
  p₀ := I.evaluation B false
  p₁ := I.evaluation B true
  ι := I.constant B
  ι_p₀ := I.constant_evaluation B false
  ι_p₁ := I.constant_evaluation B true


/-- 概要：区間からの内部 Hom は複体の自己関手（BF §3.1）。
方針：値域の chain map の後合成を用いる。
規約：区間の複体は固定する。
使われ方：path object の関手性の底の自己関手となる。 -/
def pathComplexFunctor (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) : Complex A ⥤ Complex A :=
  homFunctor I.coalgebra.carrier

/-- 概要：定数関数への射は値域について自然（BF §3.1）。
方針：単位からの内部 Hom の比較の自然性と前合成・後合成の交換を使う。
規約：底の複体の全 chain map について述べる。
使われ方：functorial path object の自然な第一射となる。 -/
def constantNat (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) : 𝟭 (Complex A) ⟶ I.pathComplexFunctor where
  app B := I.constant B
  naturality {B B'} f := by
    have hU := (MonoidalClosed.unitNatIso (C := Complex A)).hom.naturality f
    change f ≫ (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B')).inv =
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).inv ≫
        homPostcompose (𝟙_ (Complex A)) f at hU
    change f ≫ ((MonoidalClosed.unitIsoSelf (C := Complex A) (X := B')).inv ≫
      homPrecompose I.contraction B') =
      ((MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).inv ≫
        homPrecompose I.contraction B) ≫ homPostcompose I.coalgebra.carrier f
    rw [← Category.assoc, hU, Category.assoc, homPostcompose_precompose, Category.assoc]

/-- 概要：端点評価は値域について自然（BF §3.1）。
方針：Hom の前合成・後合成の交換と単位比較の自然性を使う。
規約：両端点で同じ証明を使う。
使われ方：functorial path object の二つの自然な評価射となる。 -/
def evaluationNat (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (b : Bool) :
    I.pathComplexFunctor ⟶ 𝟭 (Complex A) where
  app B := I.evaluation B b
  naturality {B B'} f := by
    have hU := (MonoidalClosed.unitNatIso (C := Complex A)).inv.naturality f
    change homPostcompose (𝟙_ (Complex A)) f ≫
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B')).hom =
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom ≫ f at hU
    change homPostcompose I.coalgebra.carrier f ≫
      (homPrecompose (I.endpoint b) B' ≫
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B')).hom) =
      (homPrecompose (I.endpoint b) B ≫
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom) ≫ f
    rw [← Category.assoc, homPostcompose_precompose, Category.assoc, hU, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
