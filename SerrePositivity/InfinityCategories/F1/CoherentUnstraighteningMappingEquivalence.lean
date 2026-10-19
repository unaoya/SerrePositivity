module

public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyComparison
public import SerrePositivity.InfinityCategories.F1.SmallCoherentFamilyRecovery

/-!
概要：任意の底上の coherent な図式の unstraightening の写像空間比較は同値。
方針：普遍的な相対射の族を復元しその証拠を制限して両側の関手同型を得る。
規約：底と高次パラメーターの小ささを要求しない。
使われ方：Kerodon Corollary 5.6.0.6 の任意の底上の写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の底上の unstraightening の実際の写像空間比較は同値。
方針：普遍的な射の族の復元と同じ射を表す二つの証拠の一意性を使う。
規約：一般の非可逆変換と全高次パラメーターを含む。
使われ方：straightening の写像空間比較の主定理。 -/
lemma leftUnstraighteningMappingSpaceMap_isQCatEquivalence
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G) := by
  let Y := relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
  let T := leftUnstraighteningTransformationSpace F G
  let M := leftUnstraighteningMappingSpaceMap F G
  let f := relativeFunctorUncurry (𝟙 Y)
  have hf := relativeFunctorUncurry_projection (𝟙 Y)
  obtain ⟨t, W, hw₀, hw₁, hwp⟩ := exists_coherentFamily_recovery F G f hf
  let w : UnstraighteningFamilyWitness F G t f := ⟨W, hw₀, hw₁, hwp⟩
  have w₀ : UnstraighteningFamilyWitness F G (M ≫ t) (relativeFunctorUncurry M) := by
    simpa only [← relativeFunctorUncurry_naturality, Category.comp_id, f] using w.comp M
  have hfM := relativeFunctorUncurry_projection M
  have hleft : Nonempty (FunctorIso (M ≫ t) (𝟙 T)) :=
    UnstraighteningFamilyWitness.unique hfM w₀ (unstraighteningUniversalFamilyWitness F G)
  have hright := unstraighteningFamilyComparisonIso F G t f hf W hw₀ hw₁ hwp
  have hc : relativeFunctorCurry f hf = 𝟙 Y := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F)
    exact relativeFunctorUncurry_curry f hf
  rw [hc] at hright
  exact ⟨t, hleft, ⟨hright⟩⟩

/-- 概要：任意の底上の pinched 写像空間の比較も同値。
方針：区間模型との同値条件へ主定理を渡す。
規約：図式と底に追加条件を置かない。
使われ方：標準写像空間による完全忠実性。 -/
lemma leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningPinchedMappingSpaceMap F G) :=
  (leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence_iff F G).mpr
    (leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G)

end SerrePositivity.InfinityCategories
