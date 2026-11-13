module

public import SerrePositivity.Archive.KST.DescentConditional.DoubleCechDescent

/-!
# 各行の実降下による外側の実降下の反映

## 概要
各行が実際に降下するとき、積添字の指定降下と外側の指定降下が同値となることを証明する。

## 方針
指定外側比較は増強元で恒等、図式の各点で各行の実比較であることを使い、Fubini と指定同型で戻す。

## 規約
外側の降下を先に仮定しない。各行の増強元は外側の段ごとに異なってよい。

## 使われ方
論文 補題 3.2・3.3 の細分降下の両方向の比較。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.DoubleAugmentedCechDiagram

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  (A : DoubleAugmentedCechDiagram K L) [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：各行が実際に降下すれば積添字と外側の指定降下は同値（補題 3.2・3.3）。
方針：指定外側比較の弱同値による反映と、増強を保持する Fubini を合成する。
規約：局所化は内部構成する。使われ方：実際の混合 Čech での細分の反映。 -/
theorem descent_iff_outer
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (hrows : ∀ k, HasCechSpaceDescent L I J (A.right.obj k)) :
    HasCechSpaceDescent (K × L) I J (flatten K L A) ↔
      HasCechSpaceDescent K I J (outer K L A) :=
  (cechSpaceDescent_rowwise_iff K L I J hcof (weakEquivalences SSet.{u}).Q
    (Projective.objectwise (K × L) (weakEquivalences SSet.{u})).Q (flatten K L A)).trans
    ((cechSpaceDescent_iso_iff K I J (rowLimitIso K L A I J)).trans
      (cechSpaceDescent_map_iff_canonical K I J (outerComparison K L A I J)
        ((weakEquivalences SSet.{u}).id_mem A.left) (fun k ↦ hrows k)).symm)

end SerrePositivity.KST.Descent.DoubleAugmentedCechDiagram
