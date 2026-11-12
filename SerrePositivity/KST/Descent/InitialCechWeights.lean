module

public import SerrePositivity.KST.Descent.AugmentedCechWeightChange
public import SerrePositivity.KST.Descent.WeightedCechConeCompatibility
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen

/-!
# 始対象を持つ添字圏の指定 Čech 計算

## 概要
始対象での評価を定数図式の実際の右随伴にし、定数単位重みの射影的 cofibrancy を証明する。

## 方針
指定増強の始対象での成分から実際の Hom 同値を構成し、評価の右 Quillen 性を使う。

## 規約
一般の添字圏の定数重みが射影的 cofibrant とは仮定しない。始対象から導出する。

## 使われ方
論文 補題 3.2 の分裂余単体対象の拡張図式。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K] (k : K) (hk : IsInitial k)

include k hk

/-- 概要：始対象での評価は定数図式の実際の右随伴（補題 3.2）。
方針：増強の始対象での成分を取り、逆に始対象からの指定射で全成分を作る。
規約：任意の図式と全ての図式射についての随伴。使われ方：定数重みの導来計算。 -/
def initialCechConstantAdjunction :
    (Functor.const K : SSet.{u} ⥤ _) ⊣ (evaluation K SSet.{u}).obj k :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X F ↦
        { toFun := fun a ↦ a.app k
          invFun := fun f ↦
            { app := fun l ↦ f ≫ F.map (hk.to l)
              naturality {l m} a := by
                change 𝟙 X ≫ (f ≫ F.map (hk.to m)) = (f ≫ F.map (hk.to l)) ≫ F.map a
                rw [Category.id_comp, Category.assoc, ← F.map_comp]
                exact congrArg (fun t ↦ f ≫ F.map t) (hk.hom_ext _ _) }
          left_inv := by
            intro a
            apply NatTrans.ext
            funext l
            exact (a.naturality (hk.to l)).symm.trans (Category.id_comp _)
          right_inv := by
            intro f
            change f ≫ F.map (hk.to k) = f
            have he : hk.to k = 𝟙 k := hk.hom_ext _ _
            rw [he, F.map_id]
            exact Category.comp_id f }
      homEquiv_naturality_left_symm := by
        intro X' X F f g
        apply NatTrans.ext
        funext l
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by intro X F G a b; rfl }

/-- 概要：定数単位重みの錐空間は始対象での評価に自然同型（補題 3.2）。
方針：テンソル単位同型で定数随伴へ移し、右随伴の一意性を使う。
規約：指定随伴を保持する。使われ方：指定重み増強の計算。 -/
def initialCechConeIso :
    WeightedCones.coneSpace K ((Functor.const K).obj (𝟙_ SSet.{u})) ≅
      (evaluation K SSet.{u}).obj k :=
  ((WeightedCones.adjunction K _).ofNatIsoLeft (WeightComparison.tensorUnitIso K)).rightAdjointUniq
    (initialCechConstantAdjunction K k hk)

/-- 概要：定数重みの指定増強は始対象での指定成分そのもの（補題 3.2）。
方針：指定テンソル単位同型と同じ随伴の Hom 対応を追跡する。
規約：任意の増強つき図式に対して指定射の等式を得る。使われ方：実降下の始対象での判定。 -/
theorem initialCechConeIso_augmentation (A : AugmentedCechDiagram K) :
    (weightedCechAugmentation K ((Functor.const K).obj (𝟙_ SSet.{u})) (𝟙 _)).app A ≫
        (initialCechConeIso K k hk).hom.app A.right = A.hom.app k := by
  have he : WeightComparison.tensorComparison K
      (𝟙 ((Functor.const K).obj (𝟙_ SSet.{u}))) =
        (WeightComparison.tensorUnitIso K).hom := by
    unfold WeightComparison.tensorComparison
    exact (congrArg (· ≫ (WeightComparison.tensorUnitIso K).hom)
      ((SerrePositivity.PointwiseAdjunction.pointwise K
        (curriedTensor SSet.{u})).flip.map_id _)).trans
      (Category.id_comp _)
  change (WeightedCones.adjunction K _).homEquiv _ _
    ((WeightComparison.tensorComparison K (𝟙 _)).app A.left ≫ A.hom) ≫ _ = _
  rw [he]
  exact (congrArg (· ≫ (initialCechConeIso K k hk).hom.app A.right)
    (Adjunction.homEquiv_ofNatIsoLeft_apply (WeightedCones.adjunction K _)
      (WeightComparison.tensorUnitIso K) A.hom).symm).trans
    (cechConeMate_rightAdjointUniq
      ((WeightedCones.adjunction K _).ofNatIsoLeft (WeightComparison.tensorUnitIso K))
      (initialCechConstantAdjunction K k hk) A.hom)

variable [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- 概要：始対象があれば定数図式関手は射影的模型への左 Quillen 関手（補題 3.2）。
方針：実際の評価の右 Quillen 性と構成した定数随伴を使う。
規約：始対象のない場合には主張しない。使われ方：定数単位重みの cofibrancy。 -/
lemma initialCechConstant_isLeftQuillen :
    let := Projective.modelCategory K I J
    IsLeftQuillen (Functor.const K : SSet.{u} ⥤ _) := by
  let := Projective.modelCategory K I J
  have := Projective.evaluation_isRightQuillen K I J (C := SSet.{u}) k
  exact Quillen.isLeftQuillen_of_isRightQuillen (initialCechConstantAdjunction K k hk)

/-- 概要：始対象があれば定数単位重みは実際に射影的 cofibrant（補題 3.2）。
方針：単位空間の cofibrancy を定数左 Quillen 関手で写す。
規約：点ごとの cofibrancy からの推測ではない。使われ方：指定重み変更による実降下の判定。 -/
lemma initialCechUnitWeight_isCofibrant
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _) :
    let := Projective.modelCategory K I J
    IsCofibrant ((Functor.const K).obj (𝟙_ SSet.{u})) := by
  let := Projective.modelCategory K I J
  have := initialCechConstant_isLeftQuillen K k hk I J
  let : (Functor.const K : SSet.{u} ⥤ _).IsLeftAdjoint :=
    (initialCechConstantAdjunction K k hk).isLeftAdjoint
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{u})
  exact Quillen.isCofibrant_obj (Functor.const K) (𝟙_ SSet.{u})

end SerrePositivity.KST.Descent
