module

public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechSpaces
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-!
# 指定増強を保つ実際の Čech 降下の重み変更

## 概要
cofibrant な可縮重みによる指定増強比較と既存の実際の比較を、増強つき図式の全ての射に自然に比較する。

## 方針
相関した導来データの指定増強の式を comma 圏で束ね、模型の弱同値の飽和性で降下条件を比較する。

## 規約
弱同値の反映も既存の模型の定理から導く。指定増強・重み増強を置き換えない。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech、分裂降下、細分の実際の指定比較。
-/

@[expose] public section

noncomputable section

universe u vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable (W : K ⥤ SSet.{u})
  (hW : let := Projective.modelCategory K I J; IsCofibrant W)
  (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
  (hq : ∀ k, weakEquivalences SSet.{u} (q.app k))
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]
  (constant : H ⥤ D)
  (e : (Functor.const K : SSet.{u} ⥤ _) ⋙ Q ≅ Λ ⋙ constant)

/-- 概要：実際の重み変更と指定増強の可換式は図式全体で自然（補題 3.2・3.3）。
方針：相関した計算の指定増強の式を各 comma 対象に適用する。
規約：増強元・図式・増強を同時に変える全ての射に自然。
使われ方：降下比較の retract と二重 Čech の指定増強の比較。 -/
theorem computedWeightedCechAugmentation_weightChange :
    Functor.whiskerRight (computedWeightedCechAugmentation K I J W q) Λ ≫
        Functor.whiskerLeft (cechAugmentedDiagram K)
          (CofibrantCechWeight.comparisonIso K I J W hW q hq hcof Λ Q constant e).hom =
      Functor.whiskerRight (homotopyCechAugmentation K I J) Λ := by
  apply NatTrans.ext
  funext A
  exact CofibrantCechWeight.comparisonIso_augmentation K I J W hW q hq hcof Λ Q constant e
    A.left A.right A.hom

include hW hq hcof Q e in
/-- 概要：局所化後の指定増強の同型性は重み変更で不変（補題 3.2）。
方針：指定増強を保つ自然同型の可換式と同型射との合成の消去を使う。
規約：任意の増強つき図式に適用する。使われ方：実際の弱同値による降下条件の比較。 -/
theorem computedWeightedCechAugmentation_isIso_iff (A : AugmentedCechDiagram K) :
    IsIso (Λ.map ((computedWeightedCechAugmentation K I J W q).app A)) ↔
      IsIso (Λ.map ((homotopyCechAugmentation K I J).app A)) := by
  have h : Λ.map ((computedWeightedCechAugmentation K I J W q).app A) ≫
      (CofibrantCechWeight.comparisonIso K I J W hW q hq hcof Λ Q constant e).hom.app A.right =
        Λ.map ((homotopyCechAugmentation K I J).app A) :=
    congrArg (fun b ↦ b.app A)
      (computedWeightedCechAugmentation_weightChange K I J W hW q hq hcof Λ Q constant e)
  rw [← h]
  exact (isIso_comp_right_iff _ _).symm

include hW hq hcof Λ Q in
/-- 概要：実際の指定増強の弱同値による降下は任意の cofibrant な可縮重みで計算可能（補題 3.2）。
方針：局所化後の同型性の重み不変性と、模型の弱同値の飽和性を使う。
規約：導来定数関手とその比較は局所化の普遍性から内部で構成する。
使われ方：二重 Čech の外重みや分裂計算から元の実際の指定降下へ戻す。 -/
theorem computedWeightedCechAugmentation_descent_iff (A : AugmentedCechDiagram K) :
    weakEquivalences SSet.{u} ((computedWeightedCechAugmentation K I J W q).app A) ↔
      HasCechSpaceDescent K I J A := by
  change weakEquivalences SSet.{u} _ ↔ weakEquivalences SSet.{u} _
  rw [Quillen.weakEquivalences_iff_isIso_map Λ, Quillen.weakEquivalences_iff_isIso_map Λ]
  exact computedWeightedCechAugmentation_isIso_iff K I J W hW q hq hcof Λ Q
    (HomotopyLimit.localizedConstant K Λ Q) (HomotopyLimit.constantComparison K Λ Q) A

end SerrePositivity.KST.Descent
