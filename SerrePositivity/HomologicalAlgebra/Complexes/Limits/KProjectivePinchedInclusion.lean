module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedKProjectiveDerivedHom
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorPinchedIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedMap

/-!
# 元の K-projective Hom 同型の全複体への包含

概要：K-projective 側の実正規化 Hom 同型は、元の包含で全複体側の同じ同型を回収する。
方針：包含の実 Hom 鎖写像と元の DK/pinched 比較の自然性を使う。
規約：元の二つの正規化 Hom 同型と実 dg 包含を保つ。
使われ方：半自由出力比較と元の全複体上の自由単位の全族の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedKProjectiveHomIso_inclusion (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A X Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) Y)).hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X.val Y.val).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
  have h := _root_.SerrePositivity.ComplexLimits.doldKanHomPinchedIso_chainMap
    (D := _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) (E := Complex A) (x := X) (y := Y)
    (x' := X.val) (y' := Y.val) ((_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A).map X Y)
  have hi : _root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap (D := _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) (E := Complex A)
      (x := X) (y := Y) (x' := X.val) (y' := Y.val)
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A).map X Y) = 𝟙 _ := by
    change Functor.whiskerRight
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
        (HomologicalComplex.truncLE'Map (𝟙 _) (ComplexShape.embeddingUpIntLE 0))) _ = _
    simp
    rfl
  simp only [hi] at h
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso, _root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← h]
  change _ ≫ (SSet.uliftFunctor.{u + 1, u}.map
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A) X.val Y.val)) ≫ _) = _
  rw [SSet.uliftFunctor.map_id, Category.id_comp]

end SerrePositivity.ComplexLimits
