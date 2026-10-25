module
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactBasic
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedReflectsQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.AcyclicZero
/-!
概要：実 dg 加群の準同型と非輪状性を、同じ実導来頂点の κ-compact 性へ接続する。
方針：元の閉射の実分解辺が可逆である判定を使い、頂点同型で全 Hom の保存性を輸送する。
規約：入力加群の射影性は不要。元の加群射と同じ実分解を保持する。
使われ方：D-8 c の選択代表・分解の変更と、零加群に準同型な入力の処理。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ閉加群射が準同型なら、その両端の実導来 κ-compact 性は同値。 -/
lemma dgModuleKappaCompact_iff_of_quasiIso {κ : Cardinal.{u}}
    {M N : ModuleCategory R D} (f : M ⟶ N) (hf : moduleQuasiIso R D f) :
    dgModuleKappaCompact R D κ M ↔ dgModuleKappaCompact R D κ N := by
  let L := dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id _)
  let t := (dgModuleEdge R D f).toTruncated.map ((truncation 2).map L)
  have ht : IsIso (SSet.Truncated.HomotopyCategory.homMk t) :=
    (dgModuleResolutionInfinity_isInvertibleEdge_iff R D f).mpr hf
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk t)
  exact F2.Compact.isKappaCompact_iff_of_iso e

/-- 非輪状加群の実導来頂点は零加群と同じ κ-compact 性を持つ。 -/
lemma dgModuleKappaCompact_of_acyclic {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {M : ModuleCategory R D} (hM : moduleAcyclic R D M) :
    dgModuleKappaCompact R D κ M :=
  (dgModuleKappaCompact_iff_of_quasiIso R D (moduleZeroTo R D M)
    (moduleAcyclic_zeroTo_quasiIso R D hM)).mp (dgModuleKappaCompact_zero R D hκ)

end SerrePositivity.InfinityCategories
