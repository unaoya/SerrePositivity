module
public import SerrePositivity.KST.Fibration.RelativePullback
public import SerrePositivity.KST.SConstruction.SRelativeEvaluation

/-! # 相対 cofiber 引き戻しと共同反映の全 S_n 行への移送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- S/相対 cofiber の元の交換同型で値域を戻した、同じ S_n 行の相対引き戻し。 -/
def RelativePullback.sRow {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (n : ℕ) :
    RelativePullback (sStableModel n X) (sClosedPredicate n A) (sClosedPredicate n B) where
  total := sStableModel n D.total
  base := sStableModel n D.base
  cofiber := (sEndofunctor n).map D.cofiber ≫ (sRelativeCofiberStableIso n A B).hom
  projection := (sEndofunctor n).map D.projection
  endpoint := (sEndofunctor n).map D.endpoint ≫ (sClosedStableIso n A).hom
  isPullback := by
    have hn := sConstruction_isPullback_of_gapped_reflection D.isPullback n
      D.reflects.isGapped_iff
    apply hn.of_iso (Iso.refl _) (stableModelForget.mapIso (sRelativeCofiberStableIso n A B))
      (Iso.refl _) (stableModelForget.mapIso (sClosedStableIso n A))
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · exact congrArg Subtype.val (sRelativeCofiberStableIso_subobject n A B).symm
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
  reflects := (D.reflects.sConstruction n).postcomp_left_iso (sRelativeCofiberStableIso n A B)

/-- 同じ S_n 行の quotient は、元の quotient の後合成と端の閉部分圏比較を厳密に回収する。 -/
lemma RelativePullback.sRow_quotient {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (n : ℕ) :
    (D.sRow n).cofiber ≫ relativeCofiberQuotient (sClosedPredicate n A) (sClosedPredicate n B) =
      (sEndofunctor n).map (D.cofiber ≫ relativeCofiberQuotient A B) ≫
        (sClosedStableIso n B).hom := by
  change (_ ≫ (sRelativeCofiberStableIso n A B).hom) ≫ _ = _
  rw [Category.assoc, sRelativeCofiberStableIso_quotient, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.KST.Fibration
