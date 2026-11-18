module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteRecognition

/-!
# 元の環の Under 入力による CAlg_R の離散対象の特徴付け

概要：既存 D(R) 比較と同じ環の Under 入力について離散像の両包含を得る。
方針：元の CommAlgCat 同値の単位同型を実離散代数射として反転する。
規約：既存 discreteCAlgUnderEmbedding と同じ入力圏を使う。
使われ方：G1′ の BS 入力と離散性の述べ直し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

def discreteCAlgUnderComparisonIso (B : CommAlgCat.{u} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B))
      ((discreteCAlgUnderEmbedding A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B))) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A)
  let e := (discreteAlgebraFunctor A).mapIso (E.unitIso.app B)
  have hf : QuasiIso e.hom.hom := by
    change QuasiIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map e.hom)
    infer_instance
  have h := cAlgVertexIsoOfQuasiIso A e.hom hf
  have h' := (discreteCAlgEmbedding_vertexIso A B) ≪≫ h ≪≫
    (discreteCAlgEmbedding_vertexIso A (E.inverse.obj (E.functor.obj B))).symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso _ ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌)
    ((nerveMap E.inverse).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (E.functor.obj B))))
  rw [nerveMap_app_mk₀]
  exact h'

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def cAlgUnderlyingDiscDiscreteUnderIso (x : (CAlg_R A) _⦋0⦌) (h : cAlgUnderlyingDisc A x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x ((discreteCAlgUnderEmbedding A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj
        (zeroDegreeDiscreteAlgebra A (cAlgVertexRepresentative A x))))) :=
  cAlgUnderlyingDiscDiscreteIso A x h ≪≫ discreteCAlgUnderComparisonIso A _

theorem cAlgUnderlyingDisc_iff_discreteUnder (x : (CAlg_R A) _⦋0⦌) :
    cAlgUnderlyingDisc A x ↔ ∃ B : Under (CommRingCat.of A),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x
        ((discreteCAlgUnderEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B))) := by
  constructor
  · intro h
    exact ⟨_, ⟨cAlgUnderlyingDiscDiscreteUnderIso A x h⟩⟩
  · rintro ⟨B, ⟨e⟩⟩
    exact cAlgUnderlyingDisc_of_iso A e.symm (discreteCAlgUnderEmbedding_underlyingDisc A B)

end SerrePositivity.EInfinity.BarrattEccles
