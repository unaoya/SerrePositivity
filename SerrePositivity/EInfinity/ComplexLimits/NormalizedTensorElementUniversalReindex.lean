module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversal

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalFamily_reindex {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map θ) ≫
      normalizedTensorElementUniversalFamily A X Y c =
    normalizedTensorElementUniversalFamily A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))) := by
  dsimp only [normalizedTensorElementUniversalFamily]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, ← SSet.stdSimplex.map_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.reindex
    (c ⋙ normalizedTensorElementDegree A X Y) θ
  change θ ≫ normalizedTensorElementTerminalParameter A X Y c =
    normalizedTensorElementTerminalParameter A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (normalizedTensorElementDegree A X Y).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) at h
  rw [h, SSet.stdSimplex.map_comp, SSet.uliftFunctor.map_comp, Category.assoc,
    normalizedTensorUniversalSimplex_naturality]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
