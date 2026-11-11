module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactBasic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedReflectsQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Basic
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 同じ閉加群射が準同型なら、その両端の実導来 κ-compact 性は同値。 -/
lemma dgModuleKappaCompact_iff_of_quasiIso {κ : Cardinal.{u}}
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (f : M ⟶ N) (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id _)
  let t := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated.map ((truncation 2).map L)
  have ht : IsIso (SSet.Truncated.HomotopyCategory.homMk t) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionInfinity_isInvertibleEdge_iff R D f).mpr hf
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk t)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso e

/-- 非輪状加群の実導来頂点は零加群と同じ κ-compact 性を持つ。 -/
lemma dgModuleKappaCompact_of_acyclic {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (hM : _root_.SerrePositivity.DifferentialGraded.moduleAcyclic R D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  (dgModuleKappaCompact_iff_of_quasiIso R D (_root_.SerrePositivity.DifferentialGraded.moduleZeroTo R D M)
    (moduleAcyclic_zeroTo_quasiIso R D hM)).mp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_zero R D hκ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
