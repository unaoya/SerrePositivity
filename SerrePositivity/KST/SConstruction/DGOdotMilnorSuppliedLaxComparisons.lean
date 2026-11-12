module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityLaxComparisonInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OriginalInputConeComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOriginalLaxSupply
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareDiagramIso

/-!
概要：D2 の三つの無条件全比較を固定 ν の消費口に代入する。
方針：元二脚・恒等二脚・元 corner cone の指定比較をそのまま保持する。
規約：追加の全比較存在仮定を加えない。共通 S 長方形は別工程。
使われ方：d④② の入力充足と、Sp の指定三境界付き恒等実面認証。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元二脚の指定両射影付き全比較を無条件に供給する。
方針：D2 の公開入力を直接代入する。規約：指定射影を変更しない。
使われ方：d④② の元二脚比較。 -/
def dgOdotMilnorSuppliedOriginalLaxComparison : DGOdotMilnorOriginalLaxComparisonInput R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d

/-- 概要：恒等二脚の対角・実 cone 差を保つ全比較を無条件に供給する。
方針：D2 の四欄をそのまま代入する。規約：元固定 ν 基底を保持。
使われ方：d④② の恒等二脚比較。 -/
def dgOdotMilnorSuppliedIdentityLaxComparison : DGOdotMilnorIdentityLaxComparisonInput R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityLaxComparisonInput R d

/-- 概要：元 corner 評価と実 cone 差の全比較を無条件に供給する。
方針：D2 の元二脚・corner・cone 比較を直接代入する。
規約：追加の cone 比較引数なし。使われ方：d④② の第三入力。 -/
def dgOdotMilnorSuppliedOriginalLaxConeComparison :
    DGOdotMilnorOriginalLaxConeComparisonInput R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxConeComparisonInput R d

/-- 概要：供給された元 cone 比較は既存の残比較型を無条件に充足する。
方針：同じ元二脚比較と corner 評価の指定全同型を使う。
規約：元比較を選び直さない。使われ方：既存 SupplyWithCone の明示引数の除去。 -/
def dgOdotMilnorSuppliedOriginalConeComparison :
    DGOdotMilnorSuppliedOriginalConeComparison R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalInputConeIso R d

/-- 概要：絶対恒等提示から既存恒等実面への指定三境界付き全図式比較。
方針：既存の実面構成へ供給済み恒等二脚入力を代入する。
規約：共通 LT 長方形への接続認証とは区別する。
使われ方：Sp 正本の VerdierSquareDiagramIso による無条件の個別実右面認証。 -/
def dgOdotMilnorSuppliedIdentityRightSquareDiagramIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
      (dgOdotMilnorActualRightDiagram R d h).square
      (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
      (DGOdotMilnorIdentityLaxComparisonInput.squareBoundary R d
        (dgOdotMilnorSuppliedIdentityLaxComparison R d) h) :=
  DGOdotMilnorIdentityLaxComparisonInput.rightSquareDiagramIso R d
    (dgOdotMilnorSuppliedIdentityLaxComparison R d) h
end SerrePositivity.KST.SConstruction
