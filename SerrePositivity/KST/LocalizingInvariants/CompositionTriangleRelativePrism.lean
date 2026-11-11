module

public import SerrePositivity.KST.LocalizingInvariants.CompositionTriangleVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.RelativeMappingEdge

/-!
概要：同じ二辺を持つ元の二つの三角形を、両辺を固定した全 prism で比較する。
方針：合成対応の第一辺射影に一次元境界の相対充填を適用する。
規約：二つの元の二単体を両端に保持する。使われ方：元の Sp 三角形の標準化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TriangleComparison

variable {X : SSet.{u}} [Quasicategory X] {x y z : X _⦋0⦌}
  (e : X.Edge x y) (f : X.Edge y z) (s t : X _⦋2⦌)
  (hs₂ : X.δ 2 s = e.edge) (hs₀ : X.δ 0 s = f.edge)
  (ht₂ : X.δ 2 t = e.edge) (ht₀ : X.δ 0 t = f.edge)

def comparison : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.RelativeMappingEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x f)
    (TriangleVertex.vertex e f s hs₂ hs₀) (TriangleVertex.vertex e f t ht₂ ht₀) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeMappingEdge _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst_trivialKanFibration x f).mem _ _
    ((TriangleVertex.vertex_first e f s hs₂ hs₀).trans
      (TriangleVertex.vertex_first e f t ht₂ ht₀).symm)

def prism : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  (Δ[2] ◁ SSet.yonedaEquiv.symm (comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.edge) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x f

lemma prism_zero : (Δ[2] ◁ stdSimplex.δ (1 : Fin 2)) ≫ prism e f s t hs₂ hs₀ ht₂ ht₀ =
    TriangleVertex.family s := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source (comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.toTruncated
  rw [prism, ← Category.assoc, ← whiskerLeft_comp]
  exact (congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x f ↦
    (Δ[2] ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x f) he).trans
      (TriangleVertex.evaluation e f s hs₂ hs₀)

lemma prism_one : (Δ[2] ◁ stdSimplex.δ (0 : Fin 2)) ≫ prism e f s t hs₂ hs₀ ht₂ ht₀ =
    TriangleVertex.family t := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target (comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.toTruncated
  rw [prism, ← Category.assoc, ← whiskerLeft_comp]
  exact (congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x f ↦
    (Δ[2] ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x f) he).trans
      (TriangleVertex.evaluation e f t ht₂ ht₀)

lemma first_map : SSet.yonedaEquiv.symm (comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.edge ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x f =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) : (Δ[1] : SSet.{u}) ⟶ _) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (comparison e f s t hs₂ hs₀ ht₂ ht₀).over.trans
    (congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) (TriangleVertex.vertex_first e f s hs₂ hs₀))

lemma prism_first : (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    prism e f s t hs₂ hs₀ ht₂ ht₀ =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [prism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_first, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    first_map, TriangleVertex.constant_edge]

lemma prism_last : (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    prism e f s t hs₂ hs₀ ht₂ ht₀ =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm f.edge := by
  rw [prism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_last, ← Category.assoc, whiskerLeft_fst]

variable (d r : X.Edge x z) (hs₁ : X.δ 1 s = d.edge) (ht₁ : X.δ 1 t = r.edge)

def diagonalEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z).Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge r) :=
  ((comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x f)).ofEq
    (TriangleVertex.vertex_diagonal _ _ _ _ _ _ hs₁)
    (TriangleVertex.vertex_diagonal _ _ _ _ _ _ ht₁)

lemma prism_diagonal : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    prism e f s t hs₂ hs₀ ht₂ ht₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (SSet.yonedaEquiv.symm (diagonalEdge e f s t hs₂ hs₀ ht₂ ht₀ d r hs₁ ht₁).edge) := by
  rw [prism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants.TriangleComparison
