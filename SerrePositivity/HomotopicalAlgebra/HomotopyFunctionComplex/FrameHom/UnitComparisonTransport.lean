module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.UnitComparisonWeakDetection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PinchedActionEquivalences
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedTransportFamily
/-!
概要：同じ単位と弱な全 pinched 族による判定を、指定した同型で両端輸送する。
方針：元の全族三角形を同じ定値射と区間作用の公式で輸送する。
規約：単位比較自身・実関手・全パラメータを保持する。
使われ方：元の局所化源単位から既存の標準単位比較への弱同値性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits

open scoped _root_.Simplicial

/-- 概要：同じ全族三角形と指定端点同型から標準単位誘導射自身は弱同値。
方針：元の二つの弱な族を同じ同型で前後合成し、全族判定に代入する。
規約：点ごとのみへ弱めない。使われ方：標準導来単位の写像空間判定。 -/
lemma unitComparisonTransport_weak {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (U : C ⟶ D) {a b c d : C.obj (Opposite.op ⦋0⦌)}
    {z x : D.obj (Opposite.op ⦋0⦌)} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c d)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z x)
    (η : (HomotopyCategory.mk x : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) a))
    (ν : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) b))
    (p : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom b c) (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z (U.app (Opposite.op ⦋0⦌) c))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence p) (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence r)
    (hu : s.hom ≫ η ≫ (hoFunctor.map U).toFunctor.map e.hom = ν)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ν ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
      (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap U b c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U a d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (U.app (Opposite.op ⦋0⦌) d) η) := by
  let P := (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose c e.hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose a t.hom
  let R := (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (U.app (Opposite.op ⦋0⦌) c) s.inv) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose x ((hoFunctor.map U).toFunctor.map t.hom)
  have hP : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence P :=
    (hp.comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPrecompose_isQCatEquivalence_of_isIso e.hom c).isWeakHomotopyEquivalence).comp
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPostcompose_isQCatEquivalence_of_isIso t.hom a).isWeakHomotopyEquivalence
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence R :=
    (hr.comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPrecompose_isQCatEquivalence_of_isIso s.inv _).isWeakHomotopyEquivalence).comp
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPostcompose_isQCatEquivalence_of_isIso
          ((hoFunctor.map U).toFunctor.map t.hom) x).isWeakHomotopyEquivalence
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence a d).isWeakHomotopyEquivalence
  refine _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.unitComparison_weak_of_probe_family _ (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace a d) R
    (hP.comp hi) hR ?_
  have hu' : η ≫ (hoFunctor.map U).toFunctor.map e.hom = s.inv ≫ ν := by
    rw [← hu]
    simp only [Iso.inv_hom_id_assoc]
  have ht := _root_.SerrePositivity.ComplexLimits.pinchedTransport_intervalFamily (a := x) (b := z)
    (c := U.app (Opposite.op ⦋0⦌) c) (d := U.app (Opposite.op ⦋0⦌) d) s.inv
    ((hoFunctor.map U).toFunctor.map t.hom) r
  simp only [Category.assoc] at ht
  dsimp only [P, R]
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace a d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U a d), ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomToIntervalMappingSpace_naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family, _root_.SerrePositivity.ComplexLimits.pinchedTransport_forget_family]
  simp only [Category.assoc]
  rw [ht]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K η)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map e.hom)),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, hu', _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ν), hf]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
