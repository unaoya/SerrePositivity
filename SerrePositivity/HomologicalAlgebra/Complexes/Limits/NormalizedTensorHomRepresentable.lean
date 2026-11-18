module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorPinchedIso

/-!
# 実正規化テンソル Hom の同じ標準単体による族

概要：元の frame 射を同じ代表可能単体の Hom 族へ送り、実前後作用を保つ。
方針：同じ Yoneda 同値と元の実 pinched 比較を合成する。
規約：元の X⊗NΔn・射・全単体次数を保つ。
使われ方：正規化 frame 屋根の普遍評価族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def normalizedTensorHomRepresentable (X Y : Complex A) (n : SimplexCategory)
    (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) :
    SSet.stdSimplex.obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y :=
  SSet.yonedaEquiv.symm g

lemma normalizedTensorHomRepresentable_postcomp (X : Complex A) {Y Z : Complex A}
    (n : SimplexCategory) (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) (h : Y ⟶ Z) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Y n g ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).map h =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Z n (g ≫ h) := by
  apply SSet.yonedaEquiv.injective
  simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

lemma normalizedTensorHomRepresentable_reindex (X Y : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj m ⟶ Y) :
    SSet.stdSimplex.map f ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Y m g =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Y n ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f ≫ g) :=
  SSet.yonedaEquiv_symm_naturality_left
    (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y) f g

def normalizedTensorHomPinchedSimplex (X Y : Complex A) (n : SimplexCategory)
    (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) :
    SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y :=
  SSet.uliftFunctor.{u + 1, u}.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Y n g) ≫
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom

end SerrePositivity.ComplexLimits
