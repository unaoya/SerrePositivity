module

public import SerrePositivity.KST.Descent.CechReindexAugmentation
public import SerrePositivity.KST.Descent.CechFibrantDiagrams
public import SerrePositivity.KST.Descent.AugmentedCechWeightChange

/-!
# 左随伴な添字制限による実際の指定降下の比較

## 概要
左随伴な添字への制限の前後で、実際の指定ホモトピー比較の弱同値が同値であることを証明する。

## 方針
元の指定 cofibrant 重みを右随伴で移し、指定増強を保つ錐同型と独立な置換の弱同値を使う。

## 規約
指定増強と模型の置換を保持する。降下性を追加公理として仮定しない。

## 使われ方
論文 補題 3.2 の分裂余単体対象の実降下。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.CechReindex

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]
  {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b)

include adj

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- 概要：移した重みでの置換後の錐から制限後の実際の錐への指定比較（補題 3.2）。
方針：同じ錐同型と制限後の独立な指定置換比較を合成する。
規約：置換する前の図式の fibrancy は要求しない。使われ方：実降下の二つの比較を結ぶ。 -/
def computedConeComparison :
    CofibrantCechWeight.weightedFunctor L I J (weight (b := b) (HomotopyCones.weight K I J)) ⟶
      HomotopyCones.replacement L I J ⋙ precomp a ⋙ HomotopyCones.functor K I J :=
  Functor.whiskerLeft (HomotopyCones.replacement L I J)
      (coneIso adj (HomotopyCones.weight K I J)).hom ≫
    Functor.whiskerLeft (HomotopyCones.replacement L I J ⋙ precomp a)
      (HomotopyCones.comparison K I J)

/-- 概要：移した重みからの指定比較は全ての図式で実際に弱同値（補題 3.2）。
方針：射影的 fibrant 置換の制限も fibrant であり、そこでの独立な比較は弱同値となる。
規約：同型と独立な置換の比較だけを合成。使われ方：実際の降下条件の移行。 -/
theorem computedConeComparison_weakEquivalence (F : L ⥤ SSet.{u}) :
    weakEquivalences SSet.{u} ((computedConeComparison K L I J adj).app F) := by
  have hr : let := Projective.modelCategory K I J
      IsFibrant ((precomp a).obj ((HomotopyCones.replacement L I J).obj F)) := by
    apply (cechDiagram_isFibrant_iff K I J _).mpr
    intro k
    exact (cechDiagram_isFibrant_iff L I J _).mp
      (HomotopyCones.replacement_isFibrant L I J F) (a.obj k)
  exact (weakEquivalences SSet.{u}).comp_mem _ _
    (mem_weakEquivalences ((coneIso adj (HomotopyCones.weight K I J)).hom.app
      ((HomotopyCones.replacement L I J).obj F)))
    (HomotopyCones.comparison_weakEquivalence_of_fibrant K I J _ hr)

omit [IsQuillenBifunctor (curriedTensor SSet.{u})] in
/-- 概要：置換後も添字変更の比較は両方の指定増強を保持（補題 3.2）。
方針：生の錐同型の増強の式と自然性を二つの置換比較へ適用する。
規約：元の指定比較を同型から逆定義しない。使われ方：弱同値の二つの合成による実降下判定。 -/
theorem computedConeComparison_augmentation (A : AugmentedCechDiagram L) :
    (computedWeightedCechAugmentation L I J
        (weight (b := b) (HomotopyCones.weight K I J))
        (augmentation (HomotopyCones.weight K I J) (HomotopyCones.weightComparison K I J))).app A ≫
      (computedConeComparison K L I J adj).app A.right =
    (homotopyCechAugmentation K I J).app ((augmentedRestriction a).obj A) ≫
      (HomotopyCones.functor K I J).map
        ((precomp a).map ((HomotopyCones.replacementComparison L I J).app A.right)) := by
  let W := HomotopyCones.weight K I J
  let q := HomotopyCones.weightComparison K I J
  let r := (HomotopyCones.replacementComparison L I J).app A.right
  let e := coneIso adj W
  let h := (weightedCechAugmentation L (weight (b := b) W) (augmentation W q)).app A
  let t := HomotopyCones.comparison K I J
  change (h ≫ (WeightedCones.coneSpace L _).map r) ≫
      (e.hom.app ((HomotopyCones.replacement L I J).obj A.right) ≫
        t.app ((precomp a).obj ((HomotopyCones.replacement L I J).obj A.right))) = _
  have h₁ : (h ≫ (WeightedCones.coneSpace L _).map r) ≫ e.hom.app _ =
      (h ≫ e.hom.app A.right) ≫ (WeightedCones.coneSpace K W).map ((precomp a).map r) :=
    (Category.assoc _ _ _).trans
      ((congrArg (h ≫ ·) (e.hom.naturality r)).trans (Category.assoc _ _ _).symm)
  have h₂ := coneIso_augmentation adj W q A
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ t.app ((precomp a).obj ((HomotopyCones.replacement L I J).obj A.right)))
      h₁).trans
      ((congrArg (fun g ↦ (g ≫ (WeightedCones.coneSpace K W).map ((precomp a).map r)) ≫
        t.app ((precomp a).obj ((HomotopyCones.replacement L I J).obj A.right))) h₂).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((weightedCechAugmentation K W q).app ((augmentedRestriction a).obj A) ≫ ·)
            (t.naturality ((precomp a).map r))).trans (Category.assoc _ _ _).symm))))

/-- 概要：左随伴な添字への制限で実際の指定降下は同値（補題 3.2）。
方針：指定重みの移送、増強を保つ比較、二つの置換の弱同値を消去する。
規約：局所化は内部構成する。使われ方：分裂 Čech の拡張側から元の実際の降下へ戻す。 -/
theorem descent_iff
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (A : AugmentedCechDiagram L) :
    HasCechSpaceDescent L I J A ↔
      HasCechSpaceDescent K I J ((augmentedRestriction a).obj A) := by
  have hW := weight_isCofibrant adj (HomotopyCones.weight K I J) I J
    (HomotopyCones.weight_isCofibrant K I J)
  have hq : ∀ l : L, weakEquivalences SSet.{u}
      ((augmentation (HomotopyCones.weight K I J)
        (HomotopyCones.weightComparison K I J) (b := b)).app l) :=
    fun l ↦ HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J (b.obj l)
  have hweight := (computedWeightedCechAugmentation_descent_iff L I J
    (weight (b := b) (HomotopyCones.weight K I J)) hW _ hq hcof
    (weakEquivalences SSet.{u}).Q
    (Projective.objectwise L (weakEquivalences SSet.{u})).Q A).symm
  have hs := computedConeComparison_weakEquivalence K L I J adj A.right
  have ht := HomotopyCones.map_weakEquivalence K I J
    ((precomp a).map ((HomotopyCones.replacementComparison L I J).app A.right))
    (fun k ↦ HomotopyCones.replacementComparison_weakEquivalence L I J A.right (a.obj k))
  have he := computedConeComparison_augmentation K L I J adj A
  exact hweight.trans
    (((weakEquivalences SSet.{u}).postcomp_iff _ _ hs).symm.trans
      ((iff_of_eq (congrArg
        (fun g : A.left ⟶
          (HomotopyCones.functor K I J).obj (a ⋙ (HomotopyCones.replacement L I J).obj A.right) ↦
          weakEquivalences SSet.{u} g) he)).trans
        ((weakEquivalences SSet.{u}).postcomp_iff _ _ ht)))

end SerrePositivity.KST.Descent.CechReindex
