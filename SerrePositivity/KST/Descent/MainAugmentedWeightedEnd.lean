module

public import SerrePositivity.KST.Descent.MainAugmentedHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedConeUnderlying

/-!
## 概要
任意の実重み付き end に対する指定増強比較。
## 方針
増強を元の点つき錐として L9 の実 end に送り、忘却後の指定射の一致も証明する。
## 規約
重みは実単体集合の図式。Kan 性や同値性を定義に付加しない。
## 使われ方
論文 補題 3.2・3.3。τ 位相の層論を実 end の Čech 計算に置換する主経路。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.KST.Spectra


namespace SerrePositivity.KST.Descent.Main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：指定増強を元の点つき錐として読む（補題 3.2）。
方針：comma 圏の指定射を錐の脚に使う。
規約：元と全成分を保持。使われ方：実 weighted end の指定比較。 -/
def augmentationCone (A : AugmentedLimitDiagram I) : Cone A.right where
  pt := A.left
  π := A.hom

/-- 概要：実点つき weighted end への指定比較（補題 3.2）。
方針：L9 の点つき定数族による end の lift を使う。
規約：任意の重み、任意の点つき係数で定義。使われ方：Fubini の指定増強比較。 -/
def weightedEndComparison (W : I ⥤ SSet.{u}) (A : AugmentedLimitDiagram I) :
    A.left ⟶ PointedWeightedEnd.obj W A.right :=
  PointedWeightedEnd.coneComparison W (augmentationCone A)

/-- 概要：実 weighted end への指定比較は増強図式に自然（補題 3.2）。
方針：元の増強の可換性を L9 の点つき錐の自然性へ渡す。
規約：基点も実際の指定射も保持する。使われ方：実 end の細分比較。 -/
theorem weightedEndComparison_naturality (W : I ⥤ SSet.{u})
    {A B : AugmentedLimitDiagram I} (f : A ⟶ B) :
    f.left ≫ weightedEndComparison W B =
      weightedEndComparison W A ≫ PointedWeightedEnd.map W f.right := by
  exact PointedWeightedEnd.coneComparison_natural W (augmentationCone A)
    (augmentationCone B) f.left f.right (fun i ↦ congrArg (fun g ↦ g.app i) f.w)

/-- 概要：点つき実 end の指定比較は忘却後の指定比較と一致（補題 3.2）。
方針：元の点つき錐と基礎の錐の成分が定義通り一致することを使う。
規約：同型性だけで比較射の一致を省略しない。使われ方：実 BK end との接続。 -/
theorem weightedEndComparison_underlying (W : I ⥤ SSet.{u})
    (A : AugmentedLimitDiagram I) :
    (weightedEndComparison W A).right ≫ (PointedWeightedEnd.underlyingIso W A.right).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (underlyingAugmentationCone A) := by
  exact PointedWeightedEnd.underlyingIso_coneComparison W (augmentationCone A)

/-- 概要：BK 重みの場合の実 end 比較は実 homotopy limit 比較と一致（補題 3.2）。
方針：任意重みの比較式に BK 重みを代入する。
規約：比較同型は L9 の固定された underlyingIso。
使われ方：一般形状と重み付き end の二つの主経路を整合させる。 -/
theorem weightedEndComparison_bousfieldKan (A : AugmentedLimitDiagram I) :
    (weightedEndComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) A).right ≫
      (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) A.right).hom =
        (homotopyLimitComparison A).right :=
  weightedEndComparison_underlying (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) A

end SerrePositivity.KST.Descent.Main
