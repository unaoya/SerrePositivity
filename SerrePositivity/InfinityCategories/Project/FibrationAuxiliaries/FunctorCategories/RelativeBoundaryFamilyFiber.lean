module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeBoundaryFamilyPre

/-!
概要：動く底と境界の全 lift 空間の fiber を厳密な固定図式の空間へ同定する。
方針：引き戻しの fiber と相対内部 Hom の fiber の二つの同型を合成する。
規約：パラメーターごとの実際の全空間の関手を保持する。
使われ方：固定図式の比較同値を族全体の fiber に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：動く境界の族の fiber と固定底・固定境界の空間の厳密な同型。
方針：二つの既存の fiber 同型を合成する。
規約：指定したパラメーターの底と境界を実際の関手 a,v で表す。
使われ方：fiber ごとの円柱比較の移送。 -/
def relativeBoundaryFamilyStrictFiberIso {A C E B L : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) (l : L _⦋0⦌)
    (a : A ⟶ B) (v : C ⟶ E) (hv : v ≫ p = i ≫ a)
    (hz₀ : r.fst.app _ (d.app _ l) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)
    (hz₁ : r.snd.app _ (d.app _ l) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection r d) l ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ a) v hv) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyFiberIso r d l ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomBoundaryFiberIso i p r a v hv (d.app _ l) hz₀ hz₁

/-- 概要：族の fiber の同型は全空間の関手を厳密に回収する。
方針：二つの fiber 同型の包含公式を合成する。
規約：高次の関手空間への射の等式。
使われ方：同型と前合成比較の可換性。 -/
lemma relativeBoundaryFamilyStrictFiberIso_hom_ι {A C E B L : SSet.{u}}
    (i : C ⟶ A) (p : E ⟶ B) (r : internalHom.PullbackObjObj i p)
    (d : L ⟶ r.pt) (l : L _⦋0⦌) (a : A ⟶ B) (v : C ⟶ E)
    (hv : v ≫ p = i ≫ a)
    (hz₀ : r.fst.app _ (d.app _ l) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)
    (hz₁ : r.snd.app _ (d.app _ l) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) :
    (relativeBoundaryFamilyStrictFiberIso i p r d l a v hv hz₀ hz₁).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ a) v hv) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection r d) l ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry r d := by
  dsimp only [relativeBoundaryFamilyStrictFiberIso, Iso.trans_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomBoundaryFiberIso_hom_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι r.π d l

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
