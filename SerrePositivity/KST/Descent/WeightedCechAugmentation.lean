module

public import SerrePositivity.KST.Descent.WeightedCechCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyCones
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightComparison

/-!
# 二重 Čech の cofibrant な可縮重み

## 概要
二つの可縮重みの外テンソル積へ指定増強を入れ、積添字でも cofibrant な可縮重みを得る。

## 方針
二つの増強のテンソル積と単位子を合成する。弱同値の保存には左 Quillen 性を使う。

## 規約
選択された既存のホモトピー錐の重みを使い、新しい置換を仮定しない。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech の導来 Fubini と細分の比較。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  {W : K ⥤ SSet.{u}} {V : L ⥤ SSet.{u}}

/-- 概要：外重みの指定された単位重みへの増強（論文 補題 3.2）。
方針：二つの指定増強をテンソルし、単位子を合成する。
規約：積添字の全ての射への自然性を保つ。使われ方：二重重みの可縮性。 -/
def externalCechWeightAugmentation
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u})) :
    externalCechWeight K L W V ⟶ (Functor.const (K × L)).obj (𝟙_ SSet.{u}) where
  app k := (q.app k.1 ⊗ₘ r.app k.2) ≫ (λ_ (𝟙_ SSet.{u})).hom
  naturality {k l} f := by
    have hq : W.map f.1 ≫ q.app l.1 = q.app k.1 := (q.naturality f.1).trans (Category.comp_id _)
    have hr : V.map f.2 ≫ r.app l.2 = r.app k.2 := (r.naturality f.2).trans (Category.comp_id _)
    change (W.map f.1 ⊗ₘ V.map f.2) ≫
        ((q.app l.1 ⊗ₘ r.app l.2) ≫ (λ_ (𝟙_ SSet.{u})).hom) =
      ((q.app k.1 ⊗ₘ r.app k.2) ≫ (λ_ (𝟙_ SSet.{u})).hom) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, tensorHom_comp_tensorHom, hq, hr]

variable [ModelCategory SSet.{u}] [IsQuillenBifunctor (curriedTensor SSet.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)

include hcof in
/-- 概要：二つの増強が各点で弱同値なら外重みの増強も各点で弱同値（補題 3.2）。
方針：単体集合の全 cofibrancy、左右テンソルの左 Quillen 性、単位子の同型性を使う。
規約：射影的 cofibrancy と点ごとの弱同値を混同しない。
使われ方：積添字の可縮重みの構成。 -/
theorem externalCechWeightAugmentation_weakEquivalence
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u}))
    (hq : ∀ k, weakEquivalences SSet.{u} (q.app k))
    (hr : ∀ l, weakEquivalences SSet.{u} (r.app l)) (k : K × L) :
    weakEquivalences SSet.{u} ((externalCechWeightAugmentation K L q r).app k) := by
  have := WeightComparison.all_cofibrant hcof (W.obj k.1)
  have := WeightComparison.all_cofibrant hcof (V.obj k.2)
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{u})
  have : IsCofibrant (((Functor.const K).obj (𝟙_ SSet.{u})).obj k.1) :=
    WeightComparison.all_cofibrant hcof _
  have : IsCofibrant (((Functor.const L).obj (𝟙_ SSet.{u})).obj k.2) :=
    WeightComparison.all_cofibrant hcof _
  have : WeakEquivalence (q.app k.1) := ⟨hq k.1⟩
  have : WeakEquivalence (r.app k.2) := ⟨hr k.2⟩
  have := tensorRight_isLeftQuillen (V.obj k.2)
  have := tensorLeft_isLeftQuillen (𝟙_ SSet.{u})
  have hq' := map_weakEquivalence_of_cofibrant (tensorRight (V.obj k.2)) (q.app k.1)
  have hr' := map_weakEquivalence_of_cofibrant (tensorLeft (𝟙_ SSet.{u})) (r.app k.2)
  have : WeakEquivalence (q.app k.1 ▷ V.obj k.2) := hq'
  have : WeakEquivalence ((((Functor.const K).obj (𝟙_ SSet.{u})).obj k.1) ◁ r.app k.2) := hr'
  change weakEquivalences SSet.{u}
    ((q.app k.1 ⊗ₘ r.app k.2) ≫ (λ_ (𝟙_ SSet.{u})).hom)
  rw [tensorHom_def]
  exact (weakEquivalences SSet.{u}).comp_mem _ _
    ((weakEquivalences SSet.{u}).comp_mem _ _ (mem_weakEquivalences _) (mem_weakEquivalences _))
    (mem_weakEquivalences _)

variable (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：既存の二つの指定ホモトピー錐重みの外積（論文 補題 3.2）。
方針：実際の射影的 cofibrant 置換から来る二つの重みを使う。
規約：置換の存在は既存の構成から導かれている。使われ方：二重 Čech の導来比較。 -/
abbrev homotopyCechProductWeight : K × L ⥤ SSet.{u} :=
  externalCechWeight K L (HomotopyCones.weight K I J) (HomotopyCones.weight L I J)

/-- 概要：指定外重みは積添字の射影的模型で cofibrant（論文 補題 3.2）。
方針：構成済みの各重みの cofibrancy と外テンソル積の保存を使う。
規約：積添字上の cofibrancy を入力しない。使われ方：実際の重みつき右 Quillen 関手。 -/
theorem homotopyCechProductWeight_isCofibrant :
    let := Projective.modelCategory (K × L) I J
    IsCofibrant (homotopyCechProductWeight K L I J) :=
  externalCechWeight_isCofibrant K L I J _ _
    (HomotopyCones.weight_isCofibrant K I J) (HomotopyCones.weight_isCofibrant L I J)

include hcof in
/-- 概要：指定外重みの増強は各積添字で弱同値（論文 補題 3.2）。
方針：既存の二つの重みの増強の弱同値をテンソル積へ移す。
規約：実際に指定された増強を使う。使われ方：ホモトピー極限の重みの比較。 -/
theorem homotopyCechProductWeightAugmentation_weakEquivalence (k : K × L) :
    weakEquivalences SSet.{u}
      ((externalCechWeightAugmentation K L (HomotopyCones.weightComparison K I J)
        (HomotopyCones.weightComparison L I J)).app k) :=
  externalCechWeightAugmentation_weakEquivalence K L hcof _ _
    (HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J)
    (HomotopyCones.weightComparison_objectwiseWeakEquivalence L I J) k

end SerrePositivity.KST.Descent
