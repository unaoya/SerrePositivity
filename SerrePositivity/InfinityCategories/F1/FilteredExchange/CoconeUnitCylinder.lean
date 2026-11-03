module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationPrism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationVertex

/-!
概要：native な余錐の単位の実円柱を、元の join の円柱として表示する。
方針：一点パラメータ付きの厳密な式から右単位子を除く。
規約：変換の代表を変更しない。使われ方：動く余錐の単位の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一点のパラメータを補った、元の図式から余錐の頂点への join 円柱。 -/
def coconeUnitCylinderMap (K : SSet.{u}) : K ⊗ (Δ[1] : SSet.{u}) ⟶ join K Δ[0] :=
  lift (𝟙 _) (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) ≫
    joinCylinderMap K Δ[0]

/-- 元の余錐から回収した単位円柱は、元の join 円柱の評価そのもの。 -/
lemma coconeTransformationHomotopy_h {K X : SSet.{u}} {f : K ⟶ X}
    (c : JoinCocone f) :
    (coconeTransformationHomotopy c).h = coconeUnitCylinderMap K ≫ c.val := by
  have h := coconeTransformationVertex_prism c
  rw [constantTransformationPrism_vertex] at h
  have e := congrArg (fun q => lift (𝟙 (K ⊗ (Δ[1] : SSet.{u})))
    (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) ≫ q) h
  simpa only [← Category.assoc, lift_fst, Category.id_comp, coconeUnitCylinderMap,
    coconeTransformationHomotopy] using e

end SerrePositivity.InfinityCategories.F2
