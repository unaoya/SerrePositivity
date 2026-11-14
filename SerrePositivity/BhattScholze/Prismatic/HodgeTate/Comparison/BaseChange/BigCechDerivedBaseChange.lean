module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineCompletedTensor
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover

/-!
# 大きい affine 項の導来完備底変換の計算

## 概要
大きい affine 枠の各項の完備テンソルは、二座標完備導来底変換を計算する。

## 方針
完備自由 δ 環の完全平坦性と有界 prism 上の離散性を使い、実際の H⁰ の線形比較を合成する。

## 規約
源の完全平坦性と終域の有界性を型に明記する。係数射の通常の平坦性は仮定しない。

## 使われ方
BS 著者版 Proposition 3.13 (2)、Theorem 6.4 の大きい結晶の橋の各項の導来計算。
-/

public noncomputable section
open CategoryTheory
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B) (hQ : IsBoundedPrism Q)
variable (f : OrientedPrism.Hom P Q) [Algebra A R]

/-- 完全平坦な代数の実際の完備テンソルが、有界 prism への完備導来底変換を計算する。 -/
def prismCompletedTensorDerivedBaseChangeIso
    (hR : IsCompletelyFlat (Ideal.span {(p : A), P.generator}) R) :
    letI := f.toRingHom.toAlgebra
    let T := PrismCompletedTensor (A := A) (C := R) Q
    letI := (prismCompletedTensorLeft Q (A := A) (C := R)).toAlgebra
    let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R))
    Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B T) := by
  let := f.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := A) (C := R) Q
  let := (prismCompletedTensorLeft Q (A := A) (C := R)).toAlgebra
  let I := Ideal.span {(p : A), P.generator}
  have hg : I.map f.toRingHom = Ideal.span {(p : B), Q.generator} := by
    change (Ideal.span {(p : A), P.generator}).map f.toRingHom = _
    rw [← Set.singleton_union, Ideal.span_union, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, map_natCast]
    change Ideal.span {(p : B)} ⊔ P.ideal.map f.toRingHom = _
    rw [f.map_ideal_eq, OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union]
  let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R))
  have hy : IsDerivedCompletelyFlat (Ideal.span {(p : B), Q.generator}) Y :=
    pairCompletedBaseChange_completelyFlat f.toRingHom I (p : B) Q.generator hg hR
  have hd : IsComplete B Q.generator Y.obj :=
    derivedComplexCompletionFunctor_isComplete B Q.generator _
  have hp : IsComplete B (p : B) Y.obj := complete_completion_of_complete (p : B) Q.generator _
    (derivedComplexCompletionFunctor_isComplete B (p : B) _)
  have ht := derivedCompletelyFlat_isDiscrete_of_boundedPrism Q hQ Y hp hd hy
  let := ht.1
  let := ht.2.1
  exact normalizedPureHomologyIso Y.obj 0 ≪≫
    (DerivedCategory.singleFunctor (ModuleCat B) 0).mapIso
      (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := R) Q).toModuleIso

variable (hP : IsBoundedPrism P) (T : Poly (A ⧸ P.ideal)) (n : ℕ)

private theorem affineBigBase :
    (affineBigCechTerm P T n hP).base.toRingHom = completedFreeDeltaBase P (BigCechIndex P T n) :=
  affineBigUnit_base P T n

/-- 大きい affine 項は基底の二座標について完全平坦。 -/
theorem affineBigCechTerm_completelyFlat :
    letI := (affineBigCechTerm P T n hP).base.toRingHom.toAlgebra
    IsCompletelyFlat (Ideal.span {(p : A), P.generator}) (affineBigCechTerm P T n hP).carrier := by
  rw [affineBigBase P hP T n]
  exact completedFreeDelta_completelyFlat P hP (BigCechIndex P T n)

/-- 大きい affine 枠の各項の完備テンソルが、完備導来底変換を計算する。 -/
def bigCechTermCompletedDerivedBaseChangeIso :
    letI := (affineBigCechTerm P T n hP).base.toRingHom.toAlgebra
    letI := f.toRingHom.toAlgebra
    let S := PrismCompletedTensor (A := A) (C := (affineBigCechTerm P T n hP).carrier) Q
    letI := (prismCompletedTensorLeft Q
      (A := A) (C := (affineBigCechTerm P T n hP).carrier)).toAlgebra
    let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (affineBigCechTerm P T n hP).carrier))
    Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B S) := by
  let := (affineBigCechTerm P T n hP).base.toRingHom.toAlgebra
  exact prismCompletedTensorDerivedBaseChangeIso P Q hQ f
    (affineBigCechTerm_completelyFlat P hP T n)

section Crystalline
variable [Algebra A B] (hg : Q.generator = (p : B))

private def crystallineTensorLinearEquiv :
    letI := (prismCompletedTensorLeft Q (A := A) (C := R)).toAlgebra
    PrismCompletedTensor (A := A) (C := R) Q ≃ₗ[B] CompletedRing p (B ⊗[A] R) := by
  let := (prismCompletedTensorLeft Q (A := A) (C := R)).toAlgebra
  let e := crystallineCompletedTensorRingEquiv (A := A) (C := R) Q hg
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro b x
  change e (prismCompletedTensorLeft Q b * x) = algebraMap B (CompletedRing p (B ⊗[A] R)) b * e x
  rw [map_mul]
  exact congrArg (· * e x) (crystallineCompletedTensorRingEquiv_left Q hg b)
end Crystalline

/-- 結晶的な終域では、各項の H⁰ 完備係数拡大そのものが二座標完備導来底変換を計算する。 -/
def bigCechTermPointwiseDerivedBaseChangeIso (hg : Q.generator = (p : B)) :
    letI := (affineBigCechTerm P T n hP).base.toRingHom.toAlgebra
    let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (affineBigCechTerm P T n hP).carrier))
    Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat B) 0).obj
      ((pCompletedScalarExtensionFunctor p f.toRingHom).obj
        (ModuleCat.of A (affineBigCechTerm P T n hP).carrier)) := by
  let := (affineBigCechTerm P T n hP).base.toRingHom.toAlgebra
  let := f.toRingHom.toAlgebra
  let R := (affineBigCechTerm P T n hP).carrier
  letI := (prismCompletedTensorLeft Q (A := A) (C := R)).toAlgebra
  exact bigCechTermCompletedDerivedBaseChangeIso P Q hQ f hP T n ≪≫
    (DerivedCategory.singleFunctor (ModuleCat B) 0).mapIso
      ((crystallineTensorLinearEquiv (R := R) Q hg).toModuleIso ≪≫
        (pCompletedScalarExtensionTensorIso p A B R).symm)

end SerrePositivity.BhattScholze.Prismatic
