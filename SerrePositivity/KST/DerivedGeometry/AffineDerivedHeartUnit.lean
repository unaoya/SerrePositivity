module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedSingleUnit
public import SerrePositivity.KST.DerivedGeometry.TriangulatedUnitLocus

/-!
概要：一つの次数に集中する加群導来対象ではアフィン導来単位は同型。
方針：シフトして心へ移し、単一加群との実際の同型を使う。
規約：対象を単一加群と等しいと仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限振幅の帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：標準 t 構造の心の全対象でアフィン導来単位は同型。
方針：導来圏の心の対象を単一加群と同型にし、単位の自然性で移す。
規約：元の加群導来圏の対象で判定する。
使われ方：TT §3、Toën §3.2 の有限振幅の帰納。
-/
lemma affineDerivedPlus_unit_heart_isIso (K : DerivedCategory.Plus (ModuleCat.{u} H))
    [K.IsGE 0] [K.IsLE 0] :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app K) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj K) 0
  let e' : K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj M :=
    ObjectProperty.isoMk _ e
  exact (NatTrans.isIso_app_iff_of_iso (affineDerivedPlusAdjunction (R := R) H).unit e').mpr
    (affineDerivedPlus_unit_single_isIso H M)

/--
概要：一つの任意の整数次数に集中する対象でアフィン導来単位は同型。
方針：その次数だけシフトして心に移し、随伴のシフト可換式で戻す。
規約：下限と上限は同じ整数。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限振幅の帰納。
-/
lemma affineDerivedPlus_unit_pure_isIso (K : DerivedCategory.Plus (ModuleCat.{u} H))
    (n : ℤ) [K.IsGE n] [K.IsLE n] :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app K) := by
  have : (K⟦n⟧).IsGE 0 := DerivedCategory.Plus.TStructure.t.isGE_shift K n n 0
  have : (K⟦n⟧).IsLE 0 := DerivedCategory.Plus.TStructure.t.isLE_shift K n n 0
  exact (adjunction_unit_isIso_iff_shift (affineDerivedPlusAdjunction (R := R) H) K n).mpr
    (affineDerivedPlus_unit_heart_isIso H (K⟦n⟧))

end SerrePositivity.KST.DerivedGeometry
