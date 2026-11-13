module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 大きい枠での完備多項式の持ち上げ

## 概要
完備多項式の係数を prism の剰余環から基底へ持ち上げる。

## 方針
主完備化 H⁰ の列による表示で、全射は主完備化後も全射となることを用いる。

## 規約
持ち上げは存在だけを使い、選択した持ち上げの自然性は仮定しない。

## 使われ方
BS 著者版 Construction 4.18 の大きい枠の座標変換。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) (f : R →+* S)

include f in
private theorem completionMap_surjective (hf : Function.Surjective f) :
    letI := principalCompletionCommRing R (p : R)
    letI := principalCompletionCommRing S (p : S)
    Function.Surjective (principalCompletionMap f (p : R) (p : S) (map_natCast f p)) := by
  let : Algebra R S := f.toAlgebra
  let := principalCompletionCommRing R (p : R)
  let := principalCompletionCommRing S (p : S)
  let g : R →ₗ[R] S := Algebra.linearMap R S
  let m : CompletedRing p R →+* CompletedRing p S :=
    principalCompletionMap f (p : R) (p : S) (map_natCast f p)
  let l : CompletedRing p R →ₗ[R] CompletedRing p S :=
    { __ := m.toAddMonoidHom
      map_smul' := fun r x => by
        change m (r • x) = r • m x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact RingHom.congr_fun (principalCompletionMap_comp f (p : R) (p : S)
          (map_natCast f p)) r }
  have h : l = principalCompletionLinearMap R p g := by
    apply principalCompletionLinearMap_ext R p (completedRing_isModuleComplete R p)
    intro r
    rw [principalCompletionLinearMap_unit]
    exact RingHom.congr_fun (principalCompletionMap_comp f (p : R) (p : S) (map_natCast f p)) r
  change Function.Surjective l
  rw [h]
  intro y
  let eR := completionEquiv R p R
  let eS := completionEquiv R p S
  obtain ⟨ys, hys⟩ := Submodule.mkQ_surjective (principalReflectionRelation S (p : S)).range (eS y)
  choose xs hxs using fun i => hf (ys i)
  refine ⟨eR.symm (principalReflectionMk R (p : R) xs), ?_⟩
  apply eS.injective
  change eS (eS.symm (reflectionLinearMap R p g
    (eR (eR.symm (principalReflectionMk R (p : R) xs))))) = eS y
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, reflectionLinearMap_mk]
  exact (congrArg (principalReflectionMk S (p : S)) (funext hxs)).trans hys

section Target

variable {T : Type u} [CommRing T] (g : R →+* T)
variable (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))

include hT in
private theorem complete_via_natCast :
    letI := g.toAlgebra
    IsModuleComplete R (p : R) (ModuleCat.of R T) := by
  let := g.toAlgebra
  apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
  change IsModuleComplete T (g (p : R)) (ModuleCat.of T T)
  rwa [map_natCast]

/-- p 完備な標的への環射を主完備化に沿って延ばす。 -/
def liftFromPolyCompletion : CompletedRing p R →+* T :=
  principalCompletionLift R (p : R) T g (complete_via_natCast p g hT)

/-- 完備化への延長は未完備環の写像に戻る。 -/
theorem liftFromPolyCompletion_comp :
    (liftFromPolyCompletion p g hT).comp (principalCompletionRingCatUnit p (CommRingCat.of R)).hom =
      g := principalCompletionLift_comp R (p : R) T g (complete_via_natCast p g hT)

/-- p 完備な環への写像は主完備化の単位上で決まる。 -/
theorem liftFromPolyCompletion_unique (l : CompletedRing p R →+* T)
    (hl : l.comp (principalCompletionRingCatUnit p (CommRingCat.of R)).hom = g) :
    l = liftFromPolyCompletion p g hT :=
  principalCompletionLift_unique R (p : R) T g (complete_via_natCast p g hT) l hl

end Target

variable {p} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (r : ℕ)

private def coefficientQuotient :
    MvPolynomial (Fin r) A →+* MvPolynomial (Fin r) (A ⧸ P.ideal) :=
  MvPolynomial.map (Ideal.Quotient.mk P.ideal)

/-- 基底係数の完備多項式環から剰余係数の完備多項式環への写像。 -/
def polyCompletionCoefficientQuotient : CompletedRing p (MvPolynomial (Fin r) A) →+*
    polyCompletion P r :=
  principalCompletionMap (coefficientQuotient P r) _ _
    (map_natCast (coefficientQuotient P r) p)

/-- 完備係数商は多項式の単位と可換。 -/
theorem polyCompletionCoefficientQuotient_unit (x : MvPolynomial (Fin r) A) :
    polyCompletionCoefficientQuotient P r
      (principalCompletionRingCatUnit p (CommRingCat.of (MvPolynomial (Fin r) A)) x) =
      prismPolynomialUnit P (Fin r) (MvPolynomial.map (Ideal.Quotient.mk P.ideal) x) :=
  RingHom.congr_fun (principalCompletionMap_comp (coefficientQuotient P r) _ _
    (map_natCast (coefficientQuotient P r) p)) x

/-- 剰余係数の完備多項式は基底係数へ持ち上がる。 -/
theorem polyCompletionCoefficientQuotient_surjective :
    Function.Surjective (polyCompletionCoefficientQuotient P r) :=
  completionMap_surjective p (coefficientQuotient P r)
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)

end SerrePositivity.BhattScholze.Prismatic
