module

public import SerrePositivity.Archive.KST.DescentConditional.SplitCechSpaceExtension
public import SerrePositivity.Archive.KST.DescentConditional.CechReindexDescent
public import SerrePositivity.Archive.KST.DescentConditional.CechDescentComparison

/-!
# 切断を持つ射の実際の指定 Čech 降下

## 概要
切断を持つ任意の射について、元の空間値前層の指定 Čech 比較が実際に弱同値となることを証明する。

## 方針
最小元を保つ添字への実際の拡張を始対象で計算し、増強を保つ添字随伴で元の Čech へ戻す。

## 規約
通常の極限や次数ごとの極限を Tot と呼ばない。実際のホモトピー比較の弱同値を結論する。

## 使われ方
論文 補題 3.2 の分裂降下と補題 3.3 の細分。原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X Y : C} (f : X ⟶ Y) (F : Cᵒᵖ ⥤ SSet.{0})

/-- 概要：元の前層からの実際の指定 Čech 空間図式（補題 3.2）。
方針：幾何の指定増強を反変に写して元の基底の値を保持する。
規約：分裂切断の選択に依存しない。使われ方：実際の降下の指定比較。 -/
def cechAugmentedPresheafSpace : AugmentedCechDiagram SimplexCategory where
  left := F.obj (op Y)
  right := (Arrow.mk f).cechNerve.rightOp ⋙ F
  hom := (Functor.constComp SimplexCategory (op Y) F).inv ≫
    Functor.whiskerRight (Arrow.mk f).augmentedCechNerve.hom.rightOp F

/-- 概要：分裂拡張の制限は元の前層の指定 Čech 増強を保持（補題 3.2）。
方針：幾何の Čech 全射と指定基底射の一致を検査する。
規約：増強元も元の基底の値のまま。使われ方：添字変更の実降下を元の比較へ移す。 -/
def splitCechAugmentedSpaceRestrictionIso (s : SplitEpi f) :
    (CechReindex.augmentedRestriction BottomSimplex.adjoin).obj
        (splitCechAugmentedSpaceExtension f s F) ≅ cechAugmentedPresheafSpace f F := Iso.refl _

variable [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：切断を持つ射の元の指定 Čech 比較は実際に弱同値（補題 3.2）。
方針：拡張側の証明済みの実降下を、増強を保持する添字変更で元の Čech へ移す。
規約：分裂降下を追加仮定にしない。使われ方：有限平坦 transfer と細分の分裂側の証明。 -/
theorem cechAugmentedPresheafSpace_descent_of_split (s : SplitEpi f)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f F) := by
  have h := (CechReindex.descent_iff SimplexCategory BottomSimplex I J
    BottomSimplex.adjunction hcof (splitCechAugmentedSpaceExtension f s F)).mp
      (splitCechAugmentedSpaceExtension_descent f s F I J hcof)
  exact (cechSpaceDescent_iso_iff SimplexCategory I J
    (splitCechAugmentedSpaceRestrictionIso f F s)).mp h

end SerrePositivity.KST.Descent
