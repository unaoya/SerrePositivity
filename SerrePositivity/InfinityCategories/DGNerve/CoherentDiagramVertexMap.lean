module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramVertices
/-!
概要：元の coherent 図式の単体を制限したときの頂点を、元の頂点へ厳密に比較する。
方針：始域の単体的自然性と定値順序写像の合成を評価する。
規約：端点を h 圏の同型へ弱めず、元の頂点の等号を保持する。
使われ方：coherent bar の面・prefix・tail の始点と終点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve R C)

lemma coherentDiagramVertex_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ j).op (I.map α.op s)) =
    coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (α.toOrderHom j)).op s) := by
  congr 1
  have h := ConcreteCategory.congr_hom
    (I.map_comp α.op (SimplexCategory.const ⦋0⦌ ⦋m⦌ j).op) s
  simpa only [← op_comp, SimplexCategory.const_comp, types_comp_apply] using h.symm

end SerrePositivity.InfinityCategories.DGNerve
