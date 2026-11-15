module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleFrameInput

/-!
# 元の全加群相対圏とモデルの宇宙表示の比較

概要：M10/C02 の同じ通常加群圏の ULiftHom・AsSmall 表示を相対関手で結ぶ。
方針：既存の二つの宇宙持ち上げ同値と N01 の同じ弱同値類の照合を使う。
規約：HA §1.3.4、対象・元の射・擬同型を変えない。
使われ方：既存のモデルの全標的普遍性を元の局所化源へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A]

/-- 概要：元の全加群の二つの宇宙表示の同じ圏同値。
方針：ULiftHom の既存同値の逆と AsSmall の既存同値を合成する。
規約：HA §1.3.4、同じ元の通常圏。使われ方：指定源の比較の単位・余単位。 -/
def strictRawModuleUniverseEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    (strictRawModuleRelativeCategory A X).category ≌
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category := by
  let := strictRawModuleModelCategory A X
  exact (ULiftHom.equiv (C := strictRawModuleCategory A X)).symm.trans AsSmall.equiv

/-- 概要：同じ元の擬同型を保つモデル表示への相対関手。
方針：同じ圏同値の順関手と N01 の弱同値類の式を使う。
規約：HA §1.3.4、追加のモデル存在仮定なし。使われ方：全標的の局所化比較。 -/
def strictRawModuleToModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleRelativeCategory A X ⟶
      SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X) := by
  let := strictRawModuleModelCategory A X
  exact {
    functor := (strictRawModuleUniverseEquivalence A X).functor
    map := by
      intro M N f hf
      change weakEquivalences (strictRawModuleCategory A X) f.down
      rw [strictRawModuleModelCategory_weakEquivalences A X]
      exact hf }

/-- 概要：同じ元の擬同型を保つ元の ULiftHom 表示への相対関手。
方針：同じ圏同値の逆関手と N01 の弱同値類の式を使う。
規約：HA §1.3.4、同じ元の射。使われ方：指定源への逆の輸送。 -/
def strictRawModuleFromModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
      (strictRawModuleCategory A X) ⟶ strictRawModuleRelativeCategory A X := by
  let := strictRawModuleModelCategory A X
  exact {
    functor := (strictRawModuleUniverseEquivalence A X).inverse
    map := by
      intro M N f hf
      change weakEquivalences (strictRawModuleCategory A X) f.down at hf
      rw [strictRawModuleModelCategory_weakEquivalences A X] at hf
      exact hf }

end SerrePositivity.EInfinity.BarrattEccles
