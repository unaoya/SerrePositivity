module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStages

/-!
概要：未完備 D-9 の同じ実二胞体を、各正段の点つき Kan 図式に保つ。
方針：元の全 Hom 作用を持つ境界商関手を、同じ四角形へ後合成する。
規約：点つき図式全体を保持する。BF 四角形の存在とは区別する。
使われ方：有限 BF 構成の正段比較と、基点固定の整数群比較の共通標的。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open Fibration NonConnective Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ未完備実四角形の正段の点つき全図式。
方針：元の境界商の厳密豊穣作用で二胞体を写す。
規約：Perf 完備化を挟まない。使われ方：全正段の指定比較の標的。 -/
def dgKappaNativeBFPointedStageSquare (r : ℕ) :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      PointedKanInfinity.{max (u + 1) v} :=
  (dgKappaNativeVerdierDiagram.{u, v} R D I).square ≫
    stableSBoundaryKanInfinityFunctor.{max (u + 1) v} r

/-- 概要：基点忘却後は元の正段全図式そのものを回収する。
方針：境界商豊穣関手の忘却式を coherent nerve の合成に使う。
規約：全四角形の厳密等号。使われ方：K-B の基点忘却した比較への接続。 -/
lemma dgKappaNativeBFPointedStageSquare_forget (r : ℕ) :
    dgKappaNativeBFPointedStageSquare.{u, v} R D I r ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched =
      dgKappaNativeBFStageSquare.{u, v} R D I r := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp
    (stableSBoundaryKanEnrichedFunctor.{max (u + 1) v} r)
    pointedKanForgetEnriched).symm
  have he := congrArg
    (fun F : EnrichedFunctor SSet.{max (u + 1) v}
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max (u + 1) v} =>
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)
    (stableSBoundaryKan_forget.{max (u + 1) v} r)
  exact (Category.assoc _ _ _).trans
    (congrArg ((dgKappaNativeVerdierDiagram.{u, v} R D I).square ≫ ·) (h.trans he))

end SerrePositivity.KST.SConstruction
