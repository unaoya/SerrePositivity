module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UniverseTriangleTimeFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitCapFamilies

/-! # 標準合成面への単位補正と宇宙輸送の交換

概要：両端の単位補正を、元の標準合成面を保ったまま共通宇宙へ移す。
方針：同じ有限単調写像が全単体で同じ再添字を与えることを照合する。
規約：元の prism と全入力を変えない。使われ方：native 係数合成三角形との実端点比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingUliftTriangleTimeFamily_first_cap_reindex {K Z : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u,v} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫ T) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexPrismFamily.{u,v} 2 T := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftTriangleTimeFamily_last_cap_reindex {K Z : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u,v} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫ T) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexPrismFamily.{u,v} 2 T := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
