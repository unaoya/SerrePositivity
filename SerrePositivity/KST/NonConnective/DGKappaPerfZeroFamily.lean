module

public import SerrePositivity.KST.NonConnective.DGKappaFullPerfAction
public import SerrePositivity.KST.SConstruction.FunctorInitialVertices

/-!
概要：実零 dg 自己関手の全 Perf 作用は、全関手空間で実際の零頂点となる。
方針：全ラベルでの零対象性を元の native 頂点へ移し、関手空間の点ごとの判定を使う。
規約：同じ一つの実零自己関手と全単体作用を保持する。
使われ方：同じ分裂四角形の零角と全族の零化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)

/-- 同じ零自己関手の Perf 作用は、元の全 native 頂点を零頂点へ送る。 -/
lemma dgKappaZeroPerfAction_values
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaZeroFunctor R D I Z))).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨X, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R
    (PresentedPerfectDGObject R (DGKappaCone R D I))).symm.surjective x
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaZeroFunctor R D I Z))).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R
            (PresentedPerfectDGObject R (DGKappaCone R D I))).symm X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
        ((presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
          (dgKappaZeroFunctor R D I Z)).obj X) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  rw [hv]
  exact dgKappaZeroPerfAction_isZeroVertex R D I Z X

/-- 同じ実零作用は、元の Perf の全関手空間で実際に始対象かつ終対象。 -/
lemma dgKappaZeroPerfFunctorVertex_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaZeroFunctor R D I Z)))) :=
  isZeroVertex_functorVertex_of_pointwise _ (dgKappaZeroPerfAction_values R D I Z)

/-- 全 native 入力作用での同じ零関手の像も、全関手空間の実零頂点。 -/
lemma dgKappaFullPerfZeroVertex_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgKappaZeroFunctor R D I Z)))) := by
  rw [dgKappaFullPerfFamilyMap_vertex]
  exact dgKappaZeroPerfFunctorVertex_isZero R D I Z

end SerrePositivity.KST.NonConnective
