module

public import SerrePositivity.KST.DerivedGeometry.DerivedSupport
public import SerrePositivity.KST.DerivedGeometry.TriangulatedKernel
public import SerrePositivity.CategoryTheory.VerdierLift

/-!
概要：開部分の補集合に台を持つ部分圏による実際の Verdier 商を構成する。
方針：台つき条件を三角関手の核と同定し、既存の Verdier 降下を使う。
規約：商から開部分への比較の同値性はここでは主張しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1、Toën §3.2 の T2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)
  [HasDerivedCategory.{w} B.Modules] [HasDerivedCategory.{w'} (B.restrict U).Modules]

/--
概要：補集合に台を持つ導来対象は三角部分圏をなす。
方針：実際の導来制限の核の三角構造へ移す。
規約：台の条件はコホモロジーで与えたものを保持する。
使われ方：Neeman 1992 Thm 2.1、TT 3.19 の台つき Verdier 商。
-/
instance supportedOnComplement_isTriangulated : (B.supportedOnComplement U).IsTriangulated := by
  rw [B.supportedOnComplement_eq_kernel U]
  infer_instance

/--
概要：全係数加群層の導来圏の台つき部分圏による Verdier 商。
方針：コホモロジーの台の条件に対応する trW を局所化する。
規約：Dqc の局所化同値や冪等完備化は仮定しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の局所化の入力。
-/
abbrev SupportedDerivedQuotient := (B.supportedOnComplement U).trW.Localization

/--
概要：台つき Verdier 商への実際の射影関手。
方針：既存の trW の局所化関手を使う。
規約：商の構成を変更しない。
使われ方：TT 3.19・8.1 の局所化正方形。
-/
def supportedDerivedProjection : DerivedCategory B.Modules ⥤ B.SupportedDerivedQuotient U :=
  (B.supportedOnComplement U).trW.Q

/--
概要：台つき Verdier 商から開部分の導来圏への比較関手。
方針：導来開制限が台つき対象を零に送る証明で既存 Verdier 降下を適用する。
規約：比較関手の同値性は別定理。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の T2。
-/
def supportedDerivedToOpen :
    B.SupportedDerivedQuotient U ⥤ DerivedCategory (B.restrict U).Modules :=
  SerrePositivity.verdierLift (B.supportedOnComplement U) (B.derivedRestriction U)
    (fun M h => (B.supportedOnComplement_iff U M).mp h)

/--
概要：台つき商を経由する比較は同じ導来開制限と自然同型。
方針：既存 Verdier 降下の因子分解同型を保持する。
規約：元の対象の導来像を保持する。
使われ方：TT 3.19・8.1、Toën §3.2 の局所化の正方形。
-/
def supportedDerivedSquare :
    B.supportedDerivedProjection U ⋙ B.supportedDerivedToOpen U ≅ B.derivedRestriction U :=
  SerrePositivity.verdierLiftFactors (B.supportedOnComplement U) (B.derivedRestriction U)
    (fun M h => (B.supportedOnComplement_iff U M).mp h)

/--
概要：台つき商から開部分への比較は整数シフトと可換。
方針：既存 Verdier 降下のシフト構造を保持する。
規約：局所化のシフトは既存のもの。
使われ方：Neeman 1992 Thm 2.1 の三角局所化。
-/
instance supportedDerivedToOpen_commShift : (B.supportedDerivedToOpen U).CommShift ℤ := by
  dsimp [supportedDerivedToOpen]
  infer_instance

/--
概要：台つき商から開部分への比較は三角関手。
方針：同じ導来制限による Verdier 降下の三角性を使う。
規約：本質的全射性・完全忠実性の仮定は追加しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の局所化の入力。
-/
instance supportedDerivedToOpen_isTriangulated : (B.supportedDerivedToOpen U).IsTriangulated := by
  dsimp [supportedDerivedToOpen]
  infer_instance

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
