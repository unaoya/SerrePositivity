module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorHomRepresentable

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma normalizedTensorHomPinchedSimplex_postcomp (X : Complex A) {Y Z : Complex A}
    (n : SimplexCategory) (g : (normalizedSimplexTensor A X).obj n ⟶ Y) (h : Y ⟶ Z) :
    normalizedTensorHomPinchedSimplex A X Y n g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X h) =
      normalizedTensorHomPinchedSimplex A X Z n (g ≫ h) := by
  dsimp only [normalizedTensorHomPinchedSimplex]
  rw [Category.assoc, ← normalizedTensorPinchedIso_postcomp, ← Category.assoc,
    ← SSet.uliftFunctor.map_comp, normalizedTensorHomRepresentable_postcomp]

lemma normalizedTensorHomPinchedSimplex_reindex (X Y : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) (g : (normalizedSimplexTensor A X).obj m ⟶ Y) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map f) ≫
      normalizedTensorHomPinchedSimplex A X Y m g =
    normalizedTensorHomPinchedSimplex A X Y n ((normalizedSimplexTensor A X).map f ≫ g) := by
  dsimp only [normalizedTensorHomPinchedSimplex]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, normalizedTensorHomRepresentable_reindex]

def normalizedTensorUniversalSimplex (X : Complex A) (n : SimplexCategory) :
    SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X ((normalizedSimplexTensor A X).obj n) :=
  normalizedTensorHomPinchedSimplex A X _ n (𝟙 _)

lemma normalizedTensorUniversalSimplex_evaluation (X Y : Complex A) (n : SimplexCategory)
    (g : (normalizedSimplexTensor A X).obj n ⟶ Y) :
    normalizedTensorUniversalSimplex A X n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X g) =
      normalizedTensorHomPinchedSimplex A X Y n g := by
  simpa only [normalizedTensorUniversalSimplex, Category.id_comp] using
    normalizedTensorHomPinchedSimplex_postcomp A X n (𝟙 _) g

lemma normalizedTensorUniversalSimplex_naturality (X : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map f) ≫
      normalizedTensorUniversalSimplex A X m =
    normalizedTensorUniversalSimplex A X n ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X ((normalizedSimplexTensor A X).map f)) := by
  rw [normalizedTensorUniversalSimplex_evaluation]
  simpa only [normalizedTensorUniversalSimplex, Category.comp_id] using
    normalizedTensorHomPinchedSimplex_reindex A X ((normalizedSimplexTensor A X).obj m) f (𝟙 _)

end SerrePositivity.EInfinity.ComplexLimits
