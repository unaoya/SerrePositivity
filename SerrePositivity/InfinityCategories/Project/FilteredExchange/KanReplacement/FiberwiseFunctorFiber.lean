module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace

/-!
概要：fiber ごとの関手の全空間の値は、元の fiber への関手空間そのもの。
方針：引き戻しの fiber 同型と内部 Hom と fiber の交換同型を合成する。
規約：値の同値ではなく厳密な同型を与える。
使われ方：fiber ごとの path 模型の値と元の図式の値との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：定値図式の頂点は、元の頂点への定値射を表す関手頂点。
方針：curry の零単体を展開する。
規約：任意の形状。使われ方：引き戻しの fiber の厳密な添字の一致。 -/
lemma constantDiagram_vertex (K B : SSet.{u}) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B).app (Opposite.op ⦋0⦌) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : K ⟶ B) := by
  let u := (SSet.unitHomEquiv B).symm b
  have hb : SSet.unitHomEquiv B u = b := (SSet.unitHomEquiv B).apply_symm_apply b
  calc
    _ = SSet.unitHomEquiv _ (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) :=
      congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B).app (Opposite.op ⦋0⦌) z) hb.symm
    _ = _ := by
      change SSet.unitHomEquiv _ (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) = SSet.unitHomEquiv _ (curry' _)
      congr 1
      apply uncurry_injective
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram, curry', uncurry_curry]
      rfl

/-- 概要：fiber ごとの関手の底の頂点 b における値は元の fiber への内部 Hom。
方針：引き戻しの fiber 同型、定値図式の頂点の式、内部 Hom の fiber 同型を合成する。
規約：fibration 性や底の充填性は不要。使われ方：元の fiber の path 空間の回収。 -/
def fiberwiseFunctorFiberIso {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p K) b ≅ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) b ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom K).map p)) (constantDiagram_vertex K B b)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihomVertexFiberIso K p b).symm

/-- 概要：fiber の同型は元の全関手空間への包含を保持する。
方針：内部 Hom の fiber 同型の包含式と、引き戻しの fiber 同型の第一射影を合成する。
規約：全パラメータで厳密に一致。使われ方：元の fiber の path と全 path 座標の照合。 -/
lemma fiberwiseFunctorFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (b : B _⦋0⦌) :
    (fiberwiseFunctorFiberIso p K b).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p K) b ≫
        pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) := by
  have transport {V W : SSet.{u}} (r : V ⟶ W) {x y : W _⦋0⦌} (h : x = y) :
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r x := by
    cases h
    exact Category.id_comp _
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) b).hom ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom K).map p)) (constantDiagram_vertex K B b)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihomVertexFiberInverse K p b) ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) = _
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihomVertexFiberInverse_comp,
    transport ((ihom K).map p) (constantDiagram_vertex K B b), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
