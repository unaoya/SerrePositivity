module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversal

/-!
概要：元の終端普遍族は、終端を変える全ての面・退化と厳密に整合する。
方針：終端パラメータの尾を保つ再添字式と元の普遍族の自然性を合成する。
規約：終端を保つ作用素だけに制限しない。
使われ方：大域 prism の全単体自然性と高次成分方程式。
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
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalFamily_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map θ) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y c =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, ← SSet.stdSimplex.map_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.reindex
    (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y) θ
  change θ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y c =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) at h
  rw [h, SSet.stdSimplex.map_comp, SSet.uliftFunctor.map_comp, Category.assoc,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_naturality]
  rfl

end SerrePositivity.ComplexLimits
