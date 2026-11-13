module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedKProjectiveDerivedHom
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPinchedIso
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedKProjectiveHomIso_inclusion (X Y : KProjectiveComplex A) :
    (normalizedKProjectiveHomIso A X Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (kProjectiveComplexInclusion A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) Y)).hom =
    (normalizedTensorPinchedIso A X.val Y.val).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
  have h := doldKanHomPinchedIso_chainMap
    (D := KProjectiveComplex A) (E := Complex A) (x := X) (y := Y)
    (x' := X.val) (y' := Y.val) ((kProjectiveComplexInclusion A).map X Y)
  have hi : doldKanHomSpaceChainMap (D := KProjectiveComplex A) (E := Complex A)
      (x := X) (y := Y) (x' := X.val) (y' := Y.val)
      ((kProjectiveComplexInclusion A).map X Y) = 𝟙 _ := by
    change Functor.whiskerRight
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
        (HomologicalComplex.truncLE'Map (𝟙 _) (ComplexShape.embeddingUpIntLE 0))) _ = _
    simp
    rfl
  simp only [hi] at h
  dsimp only [normalizedKProjectiveHomIso, normalizedTensorPinchedIso,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← h]
  change _ ≫ (SSet.uliftFunctor.{u + 1, u}.map
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A) X.val Y.val)) ≫ _) = _
  rw [SSet.uliftFunctor.map_id, Category.id_comp]

end SerrePositivity.EInfinity.ComplexLimits
