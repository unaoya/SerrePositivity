module

public import SerrePositivity.KST.Descent.DoubleAugmentedCechSpaces
public import SerrePositivity.KST.Descent.CechDescentComparison

/-!
# 各行の降下と外側の降下から二重 Čech の降下

## 概要
各行の増強元が変わる二重増強図式で、各行と外側の実際の降下から積添字の指定降下を証明する。

## 方針
各行の指定比較を点ごとの弱同値として外側の実際の関手へ送り、指定 curry 同型と Fubini で戻す。

## 規約
各行の降下・外側の降下以外に積添字の降下や指定比較の整合性は仮定しない。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech による各方向の降下の貼り合わせ。τ 位相の層論の置換。
-/

@[expose] public section

noncomputable section

universe u vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.DoubleAugmentedCechDiagram

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  (A : DoubleAugmentedCechDiagram K L) [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：元の各行の実際の指定比較の列（論文 補題 3.2）。
方針：行の関手へ指定比較を前合成する。
規約：外側の各段で増強元が異なる。使われ方：点ごとの弱同値を外側で写す。 -/
abbrev rowHomotopyComparison : A.right ⋙ cechAugmentedSource L ⟶
    (A.right ⋙ cechAugmentedDiagram L) ⋙ HomotopyCones.functor L I J :=
  Functor.whiskerLeft A.right (homotopyCechAugmentation L I J)

/-- 概要：元の各行の実際の計算への合成増強を持つ外側図式（補題 3.2）。
方針：外側増強の後に各行の実際の指定比較を合成する。
規約：元の増強元を保持する。使われ方：外側の降下による合成弱同値。 -/
abbrev rowLimitOuter : AugmentedCechDiagram K := {
  left := A.left
  right := (A.right ⋙ cechAugmentedDiagram L) ⋙ HomotopyCones.functor L I J
  hom := A.hom ≫ rowHomotopyComparison K L A I J }

/-- 概要：外側の元の図式から行の実際の計算後の図式への指定射（補題 3.2）。
方針：増強元は恒等、図式側は各行の実際の指定比較にする。
規約：合成増強の可換性を構成する。使われ方：外側比較の自然性。 -/
def outerComparison : outer K L A ⟶ rowLimitOuter K L A I J where
  left := 𝟙 A.left
  right := rowHomotopyComparison K L A I J
  w := Category.id_comp _

/-- 概要：積添字化した行の外側計算と元の各行の計算後の外側図式は同型（補題 3.2）。
方針：指定 curry/uncurry 同型を実際の内側関手で写し、増強の因子化を可換式に使う。
規約：指定増強元は恒等同型。使われ方：積添字の指定降下への移送。 -/
def rowLimitIso : rowHomotopyCechDiagram K L I J (flatten K L A) ≅ rowLimitOuter K L A I J :=
  Comma.isoMk (Iso.refl A.left)
    (Functor.isoWhiskerRight (curryIso K L A).symm (HomotopyCones.functor L I J))
    ((Category.id_comp _).trans (homotopyRowsFactorization K L A I J).symm)

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K × L ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise (K × L) (weakEquivalences SSet.{u}))]

include hcof Λ Q in
/-- 概要：各行と外側の実際の降下から積添字の実際の指定降下（補題 3.2・3.3）。
方針：点ごとの行の比較を外側で写し、外側比較の自然性・指定同型・Fubini を合成する。
規約：増強元は行ごとに異なってよい。全ての比較は構成した指定射。
使われ方：二重 Čech の Fubini による降下と細分の貼り合わせ。 -/
theorem descent (houter : HasCechSpaceDescent K I J (outer K L A))
    (hrows : ∀ k, HasCechSpaceDescent L I J (A.right.obj k)) :
    HasCechSpaceDescent (K × L) I J (flatten K L A) := by
  have hm : weakEquivalences SSet.{u}
      ((HomotopyCones.functor K I J).map (rowHomotopyComparison K L A I J)) :=
    HomotopyCones.map_weakEquivalence K I J _ (fun k ↦ hrows k)
  have hn : 𝟙 A.left ≫ (homotopyCechAugmentation K I J).app (rowLimitOuter K L A I J) =
      (homotopyCechAugmentation K I J).app (outer K L A) ≫
        (HomotopyCones.functor K I J).map (rowHomotopyComparison K L A I J) :=
    (homotopyCechAugmentation K I J).naturality (outerComparison K L A I J)
  have he : (homotopyCechAugmentation K I J).app (rowLimitOuter K L A I J) =
      (homotopyCechAugmentation K I J).app (outer K L A) ≫
        (HomotopyCones.functor K I J).map (rowHomotopyComparison K L A I J) :=
    (Category.id_comp _).symm.trans hn
  have hc : HasCechSpaceDescent K I J (rowLimitOuter K L A I J) := by
    change weakEquivalences SSet.{u}
      ((homotopyCechAugmentation K I J).app (rowLimitOuter K L A I J))
    exact Eq.mpr (congrArg (fun f : A.left ⟶ (HomotopyCones.functor K I J).obj
      ((A.right ⋙ cechAugmentedDiagram L) ⋙ HomotopyCones.functor L I J) ↦
        weakEquivalences SSet.{u} f) he)
      ((weakEquivalences SSet.{u}).comp_mem _ _ houter hm)
  exact (cechSpaceDescent_rowwise_iff K L I J hcof Λ Q (flatten K L A)).mpr
    ((cechSpaceDescent_iso_iff K I J (rowLimitIso K L A I J)).mpr hc)

include hcof in
/-- 概要：局所化を内部構成した各行と外側の降下の貼り合わせ（補題 3.2・3.3）。
方針：Mathlib の実際の局所化関手を一般の貼り合わせ定理へ渡す。
規約：局所化圏・関手を追加の入力にしない。使われ方：実際の二重 Čech 降下の共通入口。 -/
theorem descentCanonical (houter : HasCechSpaceDescent K I J (outer K L A))
    (hrows : ∀ k, HasCechSpaceDescent L I J (A.right.obj k)) :
    HasCechSpaceDescent (K × L) I J (flatten K L A) :=
  descent K L A I J hcof (weakEquivalences SSet.{u}).Q
    (Projective.objectwise (K × L) (weakEquivalences SSet.{u})).Q houter hrows

end SerrePositivity.KST.Descent.DoubleAugmentedCechDiagram
