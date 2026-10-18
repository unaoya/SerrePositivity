module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapRestrictionComparison

/-!
概要：KST §3.1 の全有限重なりの三段階の制限比較の結合整合性。
方針：二つの括弧の比較を dg 関手として書き、外積 Hom の各成分が元を変えないことを使う。
規約：有限集合の包含の結合の違いは証明の無関係性で同定する。
使われ方：有限チャート dg 図式の高次整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 四つの局所化環の三段階の dg 係数制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：三段階の有限重なり制限をまとめる二経路の dg 比較は一致する。
方針：一対象型の対象を比較し、Hom の各次数で全比較が恒等関数となることを使う。
規約：KST §3.1、環射等式の移送と標準制限比較を含めた結合整合性。
使われ方：全有限チャート dg 図式の比較の結合律。 -/
theorem finiteOverlapDGCompositionComparison_assoc (a : I → R) (i k l m : I)
    {T U V W : Finset I} (h : T ⊆ U) (g : U ⊆ V) (f : V ⊆ W)
    (hi : i ∈ T) (hk : k ∈ U) (hl : l ∈ V) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
        (DGRestriction (finiteOverlapChartMap R l m f hl).toRingHom
          (FiniteOverlapKoszulObject R a m W)))
      (finiteOverlapDGCompositionComparison R a i l m (h.trans g) f hi hl) =
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
        (finiteOverlapDGCompositionComparison R a k l m g f hk hl))
      (finiteOverlapDGCompositionComparison R a i k m h (g.trans f) hi hk) := by
  have hsingle : Subsingleton (FiniteOverlapKoszulObject R a m W) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
        (DGRestriction (finiteOverlapChartMap R l m f hl).toRingHom
          (FiniteOverlapKoszulObject R a m W)))
      (finiteOverlapDGCompositionComparison R a i l m (h.trans g) f hi hl))
    (G := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
        (finiteOverlapDGCompositionComparison R a k l m g f hk hl))
      (finiteOverlapDGCompositionComparison R a i k m h (g.trans f) hi hk))
    (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapDGCompositionComparison R a i l m (h.trans g) f hi hl).map _ _).f q)
      ((((finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
        (DGRestriction (finiteOverlapChartMap R l m f hl).toRingHom
          (FiniteOverlapKoszulObject R a m W))).map v w).f q) z) =
    (((finiteOverlapDGCompositionComparison R a i k m h (g.trans f) hi hk).map _ _).f q)
      ((((finiteOverlapDGCompositionComparison R a k l m g f hk hl).map v w).f q) z)
  rw [finiteOverlapDGCompositionComparison_apply,
    finiteOverlapRestrictionCompositionComparison_restricted_apply,
    finiteOverlapDGCompositionComparison_apply, finiteOverlapDGCompositionComparison_apply]

end SerrePositivity.KST.DerivedBlowup
