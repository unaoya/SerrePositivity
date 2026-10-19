module

public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction
public import SerrePositivity.InfinityCategories.F1.SmallUnstraighteningMappingRetraction
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationSmallness

/-!
概要：小さい底上の coherent な図式の unstraightening の写像空間比較は同値。
方針：普遍的な相対射の族を復元しその証拠を制限して両側の関手同型を得る。
規約：底は各次数で小さく strict な図式への制限は不要。
使われ方：Kerodon Corollary 5.6.0.6 の小さい底上の写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい底上の unstraightening の実際の写像空間比較は同値。
方針：普遍的な射の族の復元と同じ射を表す二つの証拠の一意性を使う。
規約：一般の非可逆変換と全高次パラメーターを含む。
使われ方：straightening の写像空間比較の小さい底の場合の主定理。 -/
lemma small_leftUnstraighteningMappingSpaceMap_isQCatEquivalence
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)] (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G) := by
  let Y := relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
  let T := leftUnstraighteningTransformationSpace F G
  let M := leftUnstraighteningMappingSpaceMap F G
  let f := relativeFunctorUncurry (𝟙 Y)
  have hf := relativeFunctorUncurry_projection (𝟙 Y)
  obtain ⟨t, W, hw₀, hw₁, hwp⟩ := exists_small_coherentFamily_recovery F G f hf
  let w : UnstraighteningFamilyWitness F G t f := ⟨W, hw₀, hw₁, hwp⟩
  have w₀ : UnstraighteningFamilyWitness F G (M ≫ t) (relativeFunctorUncurry M) := by
    simpa only [← relativeFunctorUncurry_naturality, Category.comp_id, f] using w.comp M
  have hfM := relativeFunctorUncurry_projection M
  have hleft : Nonempty (FunctorIso (M ≫ t) (𝟙 T)) :=
    UnstraighteningFamilyWitness.small_unique hfM w₀ (unstraighteningUniversalFamilyWitness F G)
  have hright := unstraighteningFamilyComparisonIso F G t f hf W hw₀ hw₁ hwp
  have hc : relativeFunctorCurry f hf = 𝟙 Y := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F)
    exact relativeFunctorUncurry_curry f hf
  rw [hc] at hright
  exact ⟨t, hleft, ⟨hright⟩⟩

end SerrePositivity.InfinityCategories
