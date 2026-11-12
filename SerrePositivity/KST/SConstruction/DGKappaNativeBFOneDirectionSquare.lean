module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFiniteInput
public import SerrePositivity.KST.SConstruction.StableOneDirectionKanComparison

/-!
概要：同じ未完備 native 一四角形の全 S₁ 商比較を構成する。
方針：元の厳密豊穣比較を同じ実四角形に制限する。
規約：BF 四角形の存在と区別する。使われ方：有限 BF 隣接段 span の比較脚。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の同じ一次方向商による未完備全四角形の Kan 像。
方針：全 Hom 作用を同じ実四角形へ後合成する。
規約：同じ二胞体を保持。使われ方：隣接段 span の源の比較。 -/
def dgKappaNativeBFOneDirectionStageSquare (r : ℕ) :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      PointedKanInfinity.{max (u + 1) v} :=
  (dgKappaNativeVerdierDiagram.{u, v} R D I).square ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableOneDirectionKanEnrichedFunctor.{max (u + 1) v} r)

/-- 概要：同じ元の S₁ 比較は native 四角形全体の点つき関手同型。
方針：構成済みの全族比較を元の二胞体へ制限する。
規約：頂点と四辺だけの比較で代用しない。使われ方：有限 BF 再帰の比較脚。 -/
def dgKappaNativeBFOneDirectionStageComparison (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaNativeBFOneDirectionStageSquare.{u, v} R D I r)
      (dgKappaNativeBFPointedStageSquare.{u, v} R D I r) :=
  (stableOneDirectionKanComparisonFunctorIso.{max (u + 1) v} r).precomp
    (dgKappaNativeVerdierDiagram.{u, v} R D I).square

end SerrePositivity.KST.SConstruction
