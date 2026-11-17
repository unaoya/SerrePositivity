module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HomInfinityEquivalenceTransport
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LocalizationComparison

/-!
概要：同じ局所化比較と指定二胞体を保つ共変 Hom の全族輸送。
方針：同じ比較同値の全 Hom 関手性と同じ三角形の全図式比較を合成する。
規約：元の K と三角形を変更せず、頂点ごとの別の同型を選ばない。
使われ方：hammock の Yoneda 比較から指定局所化の Hom 関手への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.Opposite
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {A B D : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory D]
  {F : A ⟶ B} {G : A ⟶ D} (c : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison F G)

/-- 概要：同じ K と指定二胞体に沿う正本の共変 Hom の全標的同型。
方針：元の全 Hom 比較に元の F を前合成し、同じ三角形の全図式輸送を合成する。
規約：元の K・全二胞体を保持。
使われ方：指定局所化への全 coherent 比較の最後の段階。 -/
def _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison.homInfinityTransport (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.uliftFunctor.{u + 1, u}.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (F.app (op ⦋0⦌) x))
      (SSet.uliftFunctor.{u + 1, u}.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) x)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.uliftFunctor.{u + 1, u}.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (F.app (op ⦋0⦌) x))
      (SSet.uliftFunctor.{u + 1, u}.map (F ≫ c.equivalence.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((F ≫ c.equivalence.hom).app (op ⦋0⦌) x)) := by
    simpa only [Functor.map_comp, Category.assoc, NatTrans.comp_app_apply] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.homInfinityEquivalenceTransport c.equivalence (F.app (op ⦋0⦌) x))
        (SSet.uliftFunctor.{u + 1, u}.map F)
  exact h ≪≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.homInfinityTriangleDiagramIso c.triangle x

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
