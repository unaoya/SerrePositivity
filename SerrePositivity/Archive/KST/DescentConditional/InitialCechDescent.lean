module

public import SerrePositivity.Archive.KST.DescentConditional.InitialCechWeights

/-!
# 始対象での実際の指定 Čech 降下の判定

## 概要
始対象を持つ添字圏で、実際の指定ホモトピー比較の弱同値を始対象の指定成分で判定する。

## 方針
射影的 cofibrant な定数重みの指定錐を始対象で計算し、指定 fibrant 置換の弱同値と重み変更を使う。

## 規約
指定増強を保持する。通常の極限の導来不変性や、元の図式の fibrancy を仮定しない。

## 使われ方
論文 補題 3.2 の分裂 Čech の拡張図式の降下。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K] (k : K) (hk : IsInitial k)
  [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：置換後の定数重みの指定比較は始対象の成分と置換比較の合成（補題 3.2）。
方針：始対象での指定錐の式と、同じ錐同型の置換射についての自然性を使う。
規約：独立な同型の選択をしない。使われ方：実際の指定比較の弱同値判定。 -/
theorem initialCechComputedAugmentation_fac (A : AugmentedCechDiagram K) :
    (computedWeightedCechAugmentation K I J ((Functor.const K).obj (𝟙_ SSet.{u}))
        (𝟙 _)).app A ≫
        (initialCechConeIso K k hk).hom.app ((HomotopyCones.replacement K I J).obj A.right) =
      A.hom.app k ≫ ((HomotopyCones.replacementComparison K I J).app A.right).app k := by
  let r := (HomotopyCones.replacementComparison K I J).app A.right
  let e := initialCechConeIso K k hk
  let a := (weightedCechAugmentation K ((Functor.const K).obj (𝟙_ SSet.{u})) (𝟙 _)).app A
  change (a ≫ (WeightedCones.coneSpace K _).map r) ≫ e.hom.app _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) (e.hom.naturality r)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ r.app k) (initialCechConeIso_augmentation K k hk A))))

include hk in
/-- 概要：置換後の定数重みの指定比較は始対象の指定成分で弱同値を判定（補題 3.2）。
方針：指定錐同型と置換比較の弱同値を二つの合成から消去する。
規約：元の図式の fibrancy は不要。使われ方：元の指定ホモトピー比較へ重み変更で戻す。 -/
theorem initialCechComputedAugmentation_weak_iff (A : AugmentedCechDiagram K) :
    weakEquivalences SSet.{u}
        ((computedWeightedCechAugmentation K I J ((Functor.const K).obj (𝟙_ SSet.{u}))
          (𝟙 _)).app A) ↔ weakEquivalences SSet.{u} (A.hom.app k) := by
  let e := (initialCechConeIso K k hk).app ((HomotopyCones.replacement K I J).obj A.right)
  have : IsIso e.hom := e.isIso_hom
  have he : weakEquivalences SSet.{u} e.hom := mem_weakEquivalences e.hom
  have hr := HomotopyCones.replacementComparison_weakEquivalence K I J A.right k
  have hfac := initialCechComputedAugmentation_fac K k hk I J A
  exact ((weakEquivalences SSet.{u}).postcomp_iff _ _ he).symm.trans
    ((iff_of_eq (congrArg
      (fun g : A.left ⟶ ((HomotopyCones.replacement K I J).obj A.right).obj k ↦
        weakEquivalences SSet.{u} g) hfac)).trans
      ((weakEquivalences SSet.{u}).postcomp_iff _ _ hr))

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]

include hk in
/-- 概要：始対象を持つ添字圏の実際の指定降下はその指定成分で判定（補題 3.2）。
方針：始対象から証明した定数重みの射影的 cofibrancy と、増強を保持する重み変更を使う。
規約：局所化は内部構成する。使われ方：分裂 Čech の拡張側の実際の降下。 -/
theorem cechSpaceDescent_initial_iff
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (A : AugmentedCechDiagram K) :
    HasCechSpaceDescent K I J A ↔ weakEquivalences SSet.{u} (A.hom.app k) := by
  have hW := initialCechUnitWeight_isCofibrant K k hk I J hcof
  have hq : ∀ _l : K, weakEquivalences SSet.{u} (𝟙 (𝟙_ SSet.{u})) := by
    intro l
    exact (weakEquivalences SSet.{u}).id_mem _
  exact (computedWeightedCechAugmentation_descent_iff K I J
    ((Functor.const K).obj (𝟙_ SSet.{u})) hW (𝟙 _) hq hcof
    (weakEquivalences SSet.{u}).Q
    (Projective.objectwise K (weakEquivalences SSet.{u})).Q A).symm.trans
      (initialCechComputedAugmentation_weak_iff K k hk I J A)

end SerrePositivity.KST.Descent
