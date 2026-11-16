module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangePrincipalH0
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover

/-!
# 有界な係数への完備テンソル積の完全平坦性

## 概要
p 完全平坦な代数を、有界 p ねじれを持つ係数環へ完備底変換すると p 完全平坦。
## 方針
既存の完備導来底変換の平坦剰余、離散性の判定 の離散性、実 H⁰ 比較を使う。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。底環の p 正則性を仮定しない。
## 使われ方
有限 T の包絡の剰余単位の完全平坦性。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Prismatic
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A]

/-- 概要：p 完全平坦な代数の完備テンソル積は、有界な係数環上で p 完全平坦。
方針：離散性の判定 の離散性を既存の導来完全平坦性に適用し、零次の係数線形比較へ移す。
規約：BS 著者版 Proposition 7.10。零環も含み、p の正則性は不要。
使われ方：有限 lci 包絡の剰余の完全平坦性。 -/
theorem completedTensorPrincipal_isCompletelyFlat (p : ℕ)
    (hA : IsCompletelyFlat (Ideal.span {(p : R)}) A)
    (hB : ∃ N : ℕ, ∀ (n : ℕ) (b : B), (p : B)^n * b = 0 → (p : B)^N * b = 0) :
    let T := B ⊗[R] A
    letI := principalCompletionCommRing T (p : T)
    letI : Algebra B (PrincipalCompletionH0 T (p : T)) :=
      ((principalCompletionUnitRingHom T (p : T)).comp (algebraMap B T)).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : B)}) (PrincipalCompletionH0 T (p : T)) := by
  let T := B ⊗[R] A
  letI := principalCompletionCommRing T (p : T)
  letI : Algebra B (PrincipalCompletionH0 T (p : T)) :=
    ((principalCompletionUnitRingHom T (p : T)).comp (algebraMap B T)).toAlgebra
  let X := (boundedAboveDerivedBaseChange (algebraMap R B)).obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
  let Y := (boundedAboveDerivedCompletionFunctor B (p : B)).obj X
  let Z := (boundedAboveDerivedCompletionFunctor B (p : B)).obj Y
  let I : Ideal B := Ideal.span {(p : B)}
  have hc : IsComplete B (p : B) Y.obj := derivedComplexCompletionFunctor_isComplete B (p : B) X.obj
  let e : Y ≅ Z := ObjectProperty.isoMk _ (derivedComplexCompletionUnitIso B (p : B) Y.obj hc)
  have hZ : IsDerivedCompletelyFlat I Z := by
    have hpair : ({(p : B), (p : B)} : Set B) = {(p : B)} := by ext x; simp
    have hm : (Ideal.span {(p : R)}).map (algebraMap R B) = Ideal.span {(p : B), (p : B)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast, hpair]
    have h := pairCompletedBaseChange_completelyFlat
      (algebraMap R B) (Ideal.span {(p : R)}) (p : B) (p : B) hm hA
    rw [hpair] at h
    exact h
  have hY : IsDerivedCompletelyFlat I Y := by
    let q := Ideal.Quotient.mk I
    let eq := DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso e)
    refine ⟨fun i hi => (hZ.1 i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ I)) i).mapIso eq), ?_⟩
    exact (Module.Flat.equiv_iff
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ I)) 0).mapIso eq).toLinearEquiv).mpr hZ.2
  have hp := derived_pure_of_complete_flat_reduction (p : B) Y hY.1 hY.2 hB hc
  letI := hp.1
  letI := hp.2
  let L := (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y.obj
  let eL : Y ≅ boundedAboveDerivedSingleFunctor.obj L :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso Y.obj 0)
  have hL : IsDerivedCompletelyFlat I (boundedAboveDerivedSingleFunctor.obj L) := by
    let eq := DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).mapIso eL)
    refine ⟨fun i hi => (hY.1 i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ I)) i).mapIso eq.symm), ?_⟩
    exact (Module.Flat.equiv_iff
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ I)) 0).mapIso eq).symm.toLinearEquiv).mpr hY.2
  have hf := completelyFlat_of_discrete_completelyFlat I L hL
  exact isCompletelyFlat_of_linearEquiv I
    (completedBaseChangeTensorPrincipalH0LinearEquiv R B A p) hf

end SerrePositivity.BhattScholze.Semiperfectoid
