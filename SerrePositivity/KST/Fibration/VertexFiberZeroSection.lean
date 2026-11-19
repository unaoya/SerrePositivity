module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeSectionFiberPoint

/-! # 任意の実 fiber 点を零単体切断で表し、その初頂点を厳密に回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 実 fiber 点を同じ零単体上の相対切断として表す。 -/
def vertexFiberZeroSection {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (SSet.yonedaEquiv.symm b)) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (SSet.yonedaEquiv.symm b) (SSet.yonedaEquiv.symm w.val) (by
    exact (SSet.yonedaEquiv_symm_comp w.val p).trans
      (congrArg SSet.yonedaEquiv.symm (w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))))

private lemma zeroSimplexVertex_eq_id :
    stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 零単体を全単体圏へ入れたときの初頂点は、同じ元の頂点。 -/
theorem zeroSimplexFirstVertex {B : SSet.{u}} (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex b)) = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_vertex, zeroSimplexVertex_eq_id,
    SSet.yonedaEquiv_symm_app_id]

/-- 零単体切断の初頂点の全空間の値は、元の同じ fiber 点。 -/
theorem vertexFiberZeroSection_firstVertex_val {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    (firstVertexSectionFiberPoint p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex b)
      (vertexFiberZeroSection p b w)).val = w.val := by
  rw [firstVertexSectionFiberPoint_val]
  change (SSet.yonedaEquiv.symm w.val).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = w.val
  rw [zeroSimplexVertex_eq_id, SSet.yonedaEquiv_symm_app_id]

/-- 初頂点の表示を戻すと、零単体切断の初頂点 fiber 点は元の指定点そのもの。 -/
theorem vertexFiberZeroSection_firstVertex {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    Eq.mp (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p z) _⦋0⦌) (zeroSimplexFirstVertex b))
      (firstVertexSectionFiberPoint p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex b)
        (vertexFiberZeroSection p b w)) = w := by
  apply Subtype.ext
  exact (vertexFiberPoint_eq_mp_val p (zeroSimplexFirstVertex b) _).trans
    (vertexFiberZeroSection_firstVertex_val p b w)

end SerrePositivity.KST.Fibration
