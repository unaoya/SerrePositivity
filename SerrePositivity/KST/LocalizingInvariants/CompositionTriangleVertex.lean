module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.F1CoherentCompositionCorrespondence

/-!
概要：指定した二辺を持つ元の二単体を、同じ合成三角形空間の頂点にする。
方針：零次元パラメーター上の元の三角形を curry し、第一辺と普遍評価を回収する。
規約：元の二単体を変更しない。使われ方：元の Sp 三角形と標準三角形の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TriangleVertex

variable {X : SSet.{u}} {x y z : X _⦋0⦌} (e : X.Edge x y) (f : X.Edge y z)
  (s : X _⦋2⦌) (h₂ : X.δ 2 s = e.edge) (h₀ : X.δ 0 s = f.edge)

def family : (Δ[2] : SSet.{u}) ⊗ Δ[0] ⟶ X :=
  fst Δ[2] Δ[0] ≫ SSet.yonedaEquiv.symm s

lemma face {i : Fin 3} {v w : X _⦋0⦌} (a : X.Edge v w) (ha : X.δ i s = a.edge) :
    (stdSimplex.δ i ▷ (Δ[0] : SSet.{u})) ≫ family s =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm a.edge := by
  have he : stdSimplex.δ i ≫ SSet.yonedaEquiv.symm s = SSet.yonedaEquiv.symm a.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ha
  rw [family, ← Category.assoc, whiskerRight_fst, Category.assoc, he]

lemma constant_edge {A : SSet.{u}} {v w : X _⦋0⦌} (a : X.Edge v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge a) : A ⟶ _) =
      fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm a.edge := by
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  exact congrArg (fun k : X.Edge v w ↦ fst (Δ[1] : SSet.{u}) A ≫
    SSet.yonedaEquiv.symm k.edge) hv

def pointMap : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry x f (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)) (family s)
    ((face s e h₂).trans (constant_edge e).symm) (face s f h₀)

def vertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x f) _⦋0⦌ :=
  SSet.yonedaEquiv (pointMap e f s h₂ h₀)

lemma pointMap_first : pointMap e f s h₂ h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x f =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry_first _ _ _ _ _ _

lemma vertex_first : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x f).app (Opposite.op ⦋0⦌)
    (vertex e f s h₂ h₀) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e := by
  have he := congrArg SSet.yonedaEquiv (pointMap_first e f s h₂ h₀)
  rw [SSet.yonedaEquiv_comp] at he
  exact he

lemma evaluation :
    (Δ[2] ◁ SSet.yonedaEquiv.symm (vertex e f s h₂ h₀)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x f = family s := by
  rw [vertex, Equiv.symm_apply_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry_evaluation _ _ _ _ _ _

lemma vertex_diagonal (d : X.Edge x z) (h₁ : X.δ 1 s = d.edge) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x f).app (Opposite.op ⦋0⦌) (vertex e f s h₂ h₀) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge d := by
  apply SSet.yonedaEquiv.symm.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry, ← Category.assoc, whisker_exchange,
    Category.assoc, evaluation]
  exact (face s d h₁).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry d).symm

end SerrePositivity.KST.LocalizingInvariants.TriangleVertex
