module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorHomRepresentable

/-!
# 実正規化 frame の恒等射による普遍 Hom 族と全自然性

概要：同じ X⊗NΔn の恒等射から、元の dg nerve の普遍 Hom 族を構成する。
方針：同じ実 Hom 同型の後作用と代表可能単体の全添字自然性を使う。
規約：同じ標準単体・同じ評価射を保つ。
使われ方：正規化 frame の実屋根評価の幾何的比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma normalizedTensorHomPinchedSimplex_postcomp (X : Complex A) {Y Z : Complex A}
    (n : SimplexCategory) (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) (h : Y ⟶ Z) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y n g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X h) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Z n (g ≫ h) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex]
  rw [Category.assoc, ← _root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso_postcomp, ← Category.assoc,
    ← SSet.uliftFunctor.map_comp, _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable_postcomp]

lemma normalizedTensorHomPinchedSimplex_reindex (X Y : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj m ⟶ Y) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map f) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y m g =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y n ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f ≫ g) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable_reindex]

def normalizedTensorUniversalSimplex (X : Complex A) (n : SimplexCategory) :
    SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X _ n (𝟙 _)

lemma normalizedTensorUniversalSimplex_evaluation (X Y : Complex A) (n : SimplexCategory)
    (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X g) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y n g := by
  simpa only [_root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex, Category.id_comp] using
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex_postcomp A X n (𝟙 _) g

lemma normalizedTensorUniversalSimplex_naturality (X : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map f) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X m =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X n ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f)) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_evaluation]
  simpa only [_root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex, Category.comp_id] using
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex_reindex A X ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj m) f (𝟙 _)

end SerrePositivity.ComplexLimits
