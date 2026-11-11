module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedModuleMap
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardMooreNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.MooreUliftNaturality
/-!
概要：実 pinched 空間の Moore 比較と元の Hom 鎖写像との自然性を示す。
方針：座標・標準正規化・宇宙交換の三つの可換式を合成する。
規約：同じ既存の pinchedHomMooreIso を使い、対象宇宙を独立に保つ。
使われ方：native 評価の実脚への全次数ホモロジーチャートの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

lemma dgBarCompactStandardModuleIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomModuleMap φ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso a b).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso x y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv a b n.unop.len (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv a b n.unop.len (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv x y n.unop.len).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv x y n.unop.len s)))
  rw [LinearEquiv.symm_apply_apply]

lemma dgBarCompactHomModuleMooreIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    (normalizedMooreComplex (ModuleCat.{u} R)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomModuleMap φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homModuleMooreIso a b).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homModuleMooreIso x y).hom ≫
      HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homModuleMooreIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, dgBarCompactStandardModuleIso_naturality,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardNormalizationIso_naturality]
  simp only [Category.assoc]

/-- 全次数・実 pinched 射の Moore 正規化比較の自然性。 -/
lemma dgBarCompactPinchedHomMooreIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    (normalizedMooreComplex (ModuleCat.{max u v} R)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreIso a b).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreIso x y).hom ≫
      ((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (.down ℕ)).map
        (HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap_coordinate, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ _
    (((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (.down ℕ)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homModuleMooreIso a b).hom), _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactMooreUliftIso_naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp, dgBarCompactHomModuleMooreIso_naturality, Functor.map_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
