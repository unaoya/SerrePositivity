module
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence
public import SerrePositivity.KST.SConstruction.PerfectVerdierRawSquare
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps

/-!
概要：任意の固定 dg 入力の全対象商の ν 値を、標準零 Cat^perf 頂点と比較する。
方針：元の零圏往復完全射と全零図式の指定同型で逆律を証明する。
規約：元全対象商の入力・ν 値を保持し、既存核面の公開型は変更しない。
使われ方：実核面と恒等右面に共通する指定零角比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, v} R)
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R A)
local notation "hZ" => dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R A)

/-- 概要：同じ全対象商の ν 値と標準零圏は Cat^perf 内で指定同型を持つ。
方針：元の零圏往復射と全零関手同型で逆律を示す。
規約：任意の固定厳密 dg 入力に適用する。使われ方：実零角の全図式比較。 -/
def dgKFixedNullPerfectZeroIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{max (u + 1) v} perfectZeroCategory_isIdempotentComplete)
    (perfectStableVertex (Z) (hZ)) where
  hom := perfectStableHoArrow (fromZeroCategory (Z))
    perfectZeroCategory_isIdempotentComplete (hZ)
  inv := perfectStableHoArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))
    (hZ) perfectZeroCategory_isIdempotentComplete
  hom_inv_id := by
    rw [← perfectStableHoArrow_comp]
    trans perfectStableHoArrow (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{max (u + 1) v} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory from 𝟙 _)
      perfectZeroCategory_isIdempotentComplete perfectZeroCategory_isIdempotentComplete
    · apply perfectStableHoArrow_eq_of_functorIso
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)
        (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)
    · exact perfectStableHoArrow_id _ _
  inv_hom_id := by
    rw [← perfectStableHoArrow_comp]
    trans perfectStableHoArrow (show (Z) ⟶ (Z) from 𝟙 _) (hZ) (hZ)
    · apply perfectStableHoArrow_eq_of_functorIso
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _
        (fun _ => dgFixedNullInput_isZeroCategory R _ _)
        (fun _ => dgFixedNullInput_isZeroCategory R _ _)
    · exact perfectStableHoArrow_id _ _

end SerrePositivity.KST.SConstruction
