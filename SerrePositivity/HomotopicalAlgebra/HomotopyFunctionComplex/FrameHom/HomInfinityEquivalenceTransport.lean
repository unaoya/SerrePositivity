module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：指定同値と指定二胞体に沿って正本の共変 Hom の全図式を輸送する。
方針：原本の全共変 Hom 比較を合成し、元の二胞体の反転・持ち上げを co-Yoneda へ送る。
規約：原本は読み取り専用、元の全比較射と全二胞体を保持する。
使われ方：hammock の Yoneda 比較から指定局所化への全標的比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.Opposite
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：同じ指定同値は正本の共変 Hom の全図式を同値に輸送する。
方針：正本の二つの Hom 比較と全充満忠実比較を元の順に合成する。
規約：全族の元の比較射を使用し、点ごとの比較を選び直さない。
使われ方：指定 K に沿う全 Hom 図式の輸送。 -/
def homInfinityEquivalenceTransport {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant x)
      (SSet.uliftFunctor.{u + 1, u}.map e.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (e.hom.app (op ⦋0⦌) x)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso x ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparisonIso e.hom e.isQCatEquivalence.isFullyFaithful x ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso (e.hom.app (op ⦋0⦌) x)).symm
        (SSet.uliftFunctor.{u + 1, u}.map e.hom)

/-- 概要：指定された全二胞体の源成分による共変 Hom の全図式比較。
方針：元の二胞体を反転・宇宙持ち上げしてから同じ co-Yoneda 関手で写す。
規約：元の二胞体の成分を保持する。
使われ方：同じ標的に固定した源の共役を全図式で表す。 -/
def homInfinityTriangleSourceIso {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f g : A ⟶ B} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (f.app (op ⦋0⦌) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (g.app (op ⦋0⦌) x)) := by
  have h := (e.op.ulift.{u, u + 1}).app (ULift.up (SSet.opObjEquiv.symm x))
  have k := h.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap B)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap B).app (op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (f.app (op ⦋0⦌) x))))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap B).app (op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (g.app (op ⦋0⦌) x)))) at k
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex] at k
  exact k

/-- 概要：元の全二胞体は共変 Hom への全標的合成にも同じ自然同型を与える。
方針：同じ持ち上げた二胞体を後合成し、同じ co-Yoneda 源成分を前合成する。
規約：元の f・g・二胞体 e を保持。
使われ方：指定局所化の比較三角形の保持。 -/
def homInfinityTriangleDiagramIso {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f g : A ⟶ B} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.uliftFunctor.{u + 1, u}.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (f.app (op ⦋0⦌) x))
      (SSet.uliftFunctor.{u + 1, u}.map g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (g.app (op ⦋0⦌) x)) :=
  (e.ulift.{u, u + 1}.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (f.app (op ⦋0⦌) x))) ≪≫
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.homInfinityTriangleSourceIso e x).precomp (SSet.uliftFunctor.{u + 1, u}.map g)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
