module

public import SerrePositivity.Archive.KST.DescentConditional.CechDescentRetract
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-!
# 弱同値な合成による transfer の実際の正規化

## 概要
transfer の合成が指定増強元と図式の各点で弱同値なら、実際の指定 Čech 降下を戻せることを証明する。

## 方針
弱同値で局所化した矢の圏で合成を逆にし、実際の retract と同型射の retract 安定性を使う。

## 規約
元の値域の加法性や厳密なスカラーの逆を要求しない。元の指定比較の自然性を保持する。

## 使われ方
論文 補題 3.2 の有理 transfer と局所 rank 公式。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

/-- 概要：自然な比較の両側の合成が同型なら比較は retract で同型を反映（補題 3.2）。
方針：矢の圏で合成の逆を transfer に後合成して実際の retract に正規化する。
規約：一般の値域で加法性は不要。使われ方：局所化後の実際の Čech transfer。 -/
theorem naturalComparison_isIso_of_isoComposite
    {D H : Type*} [Category* D] [Category* H]
    (source target : D ⥤ H) (comparison : source ⟶ target)
    {A B : D} (i : A ⟶ B) (r : B ⟶ A)
    [IsIso (source.map (i ≫ r))] [IsIso (target.map (i ≫ r))]
    [IsIso (comparison.app B)] : IsIso (comparison.app A) := by
  let si : Arrow.mk (comparison.app A) ⟶ Arrow.mk (comparison.app B) :=
    Arrow.homMk (source.map i) (target.map i) (comparison.naturality i)
  let sr : Arrow.mk (comparison.app B) ⟶ Arrow.mk (comparison.app A) :=
    Arrow.homMk (source.map r) (target.map r) (comparison.naturality r)
  have : IsIso ((si ≫ sr).left) := by
    change IsIso (source.map i ≫ source.map r)
    rw [← source.map_comp]
    infer_instance
  have : IsIso ((si ≫ sr).right) := by
    change IsIso (target.map i ≫ target.map r)
    rw [← target.map_comp]
    infer_instance
  have : IsIso (si ≫ sr) := Arrow.isIso_of_isIso_left_of_isIso_right _
  let h : RetractArrow (comparison.app A) (comparison.app B) := {
    i := si
    r := sr ≫ inv (si ≫ sr)
    retract := (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id _) }
  exact (MorphismProperty.isomorphisms H).of_retract h (by infer_instance)

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (CategoryTheory.MonoidalCategory.curriedTensor SSet.{u})]

/-- 概要：合成が各点で弱同値な transfer は実際の指定 Čech 降下を戻す（補題 3.2）。
方針：指定比較の自然性を局所化し、合成を矢の圏で正規化して retract を作る。
規約：局所化は内部構成する。厳密な retract 恒等式や元の値域の線形性は不要。
使われ方：各局所 rank が可逆となる有理 transfer による実降下の移行。 -/
theorem cechSpaceDescent_of_weakComposite {A B : AugmentedCechDiagram K}
    (i : A ⟶ B) (r : B ⟶ A)
    (hl : weakEquivalences SSet.{u} (i ≫ r).left)
    (hr : ∀ k, weakEquivalences SSet.{u} ((i ≫ r).right.app k))
    (hB : HasCechSpaceDescent K I J B) : HasCechSpaceDescent K I J A := by
  let Λ := (weakEquivalences SSet.{u}).Q
  have : IsIso ((cechAugmentedSource K ⋙ Λ).map (i ≫ r)) :=
    Localization.inverts Λ (weakEquivalences SSet.{u}) _ hl
  have : IsIso (((cechAugmentedDiagram K ⋙ HomotopyCones.functor K I J) ⋙ Λ).map (i ≫ r)) :=
    Localization.inverts Λ (weakEquivalences SSet.{u}) _
      (HomotopyCones.map_weakEquivalence K I J (i ≫ r).right hr)
  have : IsIso ((Functor.whiskerRight (homotopyCechAugmentation K I J) Λ).app B) :=
    Localization.inverts Λ (weakEquivalences SSet.{u}) _ hB
  apply (Quillen.weakEquivalences_iff_isIso_map Λ _).mpr
  exact naturalComparison_isIso_of_isoComposite (cechAugmentedSource K ⋙ Λ)
    ((cechAugmentedDiagram K ⋙ HomotopyCones.functor K I J) ⋙ Λ)
    (Functor.whiskerRight (homotopyCechAugmentation K I J) Λ) i r

end SerrePositivity.KST.Descent
