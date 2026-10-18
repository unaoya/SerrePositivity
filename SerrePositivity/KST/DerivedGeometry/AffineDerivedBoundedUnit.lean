module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedHeartUnit
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
概要：有限コホモロジー区間を持つ加群導来対象ではアフィン導来単位は同型。
方針：最下次数を切り出す truncation triangle に沿って振幅で帰納する。
規約：非有界対象への拡張には別の切断の議論が必要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 比較の有限区間。
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
概要：下限 a、上限 a+d の有限区間を持つ対象でアフィン導来単位は同型。
方針：d に帰納し、最下次数の純粋な対象と残りの区間を切断三角で結ぶ。
規約：切断は元の加群導来圏の標準 t 構造のもの。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の導来完全忠実性。
-/
lemma affineDerivedPlus_unit_amplitude_isIso (d : ℕ) (a : ℤ)
    (K : DerivedCategory.Plus (ModuleCat.{u} H)) [K.IsGE a] [K.IsLE (a + d)] :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app K) := by
  induction d generalizing a K with
  | zero =>
      have : K.IsLE a := by simpa using (inferInstance : K.IsLE (a + (0 : ℕ)))
      exact affineDerivedPlus_unit_pure_isIso H K a
  | succ d ih =>
      let t := DerivedCategory.Plus.TStructure.t (C := ModuleCat.{u} H)
      let L := (t.truncLE a).obj K
      let U := (t.truncGT a).obj K
      have : L.IsGE a := by dsimp [L, t]; infer_instance
      have : L.IsLE a := by dsimp [L, t]; infer_instance
      have hL : IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app L) :=
        affineDerivedPlus_unit_pure_isIso H L a
      have : U.IsGE (a + 1) := by dsimp [U, t]; infer_instance
      have hU : U.IsLE (a + (Nat.succ d : ℕ)) := by
        change t.IsLE ((t.truncGT a).obj K) (a + (Nat.succ d : ℕ))
        infer_instance
      have : U.IsLE ((a + 1) + d) := by
        convert hU using 1 <;> push_cast <;> ring
      have hUi : IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app U) := ih (a + 1) U
      have : IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app
          ((t.triangleLEGT a).obj K).obj₁) := hL
      have : IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app
          ((t.triangleLEGT a).obj K).obj₃) := hUi
      exact adjunction_unit_triangle_isIso₂ (affineDerivedPlusAdjunction (R := R) H)
        ((t.triangleLEGT a).obj K) (t.triangleLEGT_distinguished a K)

end SerrePositivity.KST.DerivedGeometry
