module
public import SerrePositivity.InfinityCategories.F1.CosliceRightRestriction
public import SerrePositivity.InfinityCategories.Stable.Cocone

/-! # 任意の right anodyne な単射による coslice の制限

概要：right anodyne な単射による余錐の制限は trivial Kan fibration。
方針：F1 の部分複体に対する充填定理を、像への同型と包含に分解して任意の単射へ移す。
規約：F1 の合成則・同型による制限・部分複体の充填を再利用する。
使われ方：S4 の貼り合わせの部分長方形上の coslice の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の right anodyne な単射による coslice の制限は trivial Kan fibration。
方針：像への同型と部分複体の包含に分解し、F1 の充填と同型不変性を合成する。
規約：X は quasicategory、射の表示を固定しない。
使われ方：S4 の有限部分図式の形の比較への適用。 -/
lemma sliceUnderRestrict_trivialKanFibration {K₀ K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : K₀ ⟶ K) [Mono f] (hf : rightAnodyneExtensions f) :
    TrivialKanFibration (sliceUnderRestrict p f) := by
  let R : K.Subcomplex := Subfunctor.range f
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : rightAnodyneExtensions R.ι :=
    (rightAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (asIso (Subfunctor.toRange f)) (Iso.refl K) (by rfl))).1 hf
  have hT := sliceUnderRestrict_trivialKanFibration_of_rightAnodyne p R hR
  have he : f = Subfunctor.toRange f ≫ R.ι := rfl
  rw [he, ← sliceUnderRestrict_comp]
  constructor
  exact trivialKanFibrations.comp_mem _ _ hT.mem (MorphismProperty.rlp_of_isIso _ _)

end SerrePositivity.InfinityCategories
