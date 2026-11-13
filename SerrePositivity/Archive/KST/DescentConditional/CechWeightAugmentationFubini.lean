module

public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechSpaces
public import SerrePositivity.Archive.KST.DescentConditional.WeightedCechAugmentation

/-!
# 外重みと反復重みの指定増強の Fubini

## 概要
外重みの指定増強は二段の指定増強に一致し、重みつき Fubini は増強つき図式全体で指定比較を保つ。

## 方針
テンソル結合子の自然性と三角恒等式を使い、指定錐の随伴像の保持へ渡す。

## 規約
二つの指定重み増強を固定し、任意の自然同型の存在で置き換えない。

## 使われ方
論文 補題 3.2・3.3 の導来 Fubini の指定増強との整合性。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

/-- 概要：単位への二つの射のテンソル増強は二段の増強と結合子を通じて一致（補題 3.2）。
方針：結合子の自然性と三角恒等式を適用する。
規約：任意のモノイダル圏で成立する。使われ方：二つの実際の重み増強の比較。 -/
theorem cechTensorAugmentation_assoc {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (X W V : C) (q : W ⟶ 𝟙_ C) (r : V ⟶ 𝟙_ C) :
    (α_ X W V).hom ≫ (X ◁ ((q ⊗ₘ r) ≫ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ X).hom =
      ((X ◁ q ≫ (ρ_ X).hom) ▷ V) ≫ (X ◁ r ≫ (ρ_ X).hom) := by
  have hn : (α_ X W V).hom ≫ X ◁ (q ⊗ₘ r) =
      ((X ◁ q) ⊗ₘ r) ≫ (α_ X (𝟙_ C) (𝟙_ C)).hom := by
    simpa only [id_tensorHom] using (associator_naturality (𝟙 X) q r).symm
  calc
    (α_ X W V).hom ≫ (X ◁ ((q ⊗ₘ r) ≫ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ X).hom =
        ((α_ X W V).hom ≫ X ◁ (q ⊗ₘ r)) ≫
          (X ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ X).hom := by simp [Category.assoc]
    _ = (((X ◁ q) ⊗ₘ r) ≫ (α_ X (𝟙_ C) (𝟙_ C)).hom) ≫
        (X ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ X).hom := by rw [hn]
    _ = ((X ◁ q) ⊗ₘ r) ≫ ((ρ_ X).hom ▷ (𝟙_ C)) ≫ (ρ_ X).hom := by
      rw [Category.assoc, triangle_assoc]
    _ = ((X ◁ q ≫ (ρ_ X).hom) ▷ V) ≫ (X ◁ r ≫ (ρ_ X).hom) := by
      simp [tensorHom_def, Category.assoc]

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  (W : K ⥤ SSet.{u}) (V : L ⥤ SSet.{u})
  (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
  (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u}))

/-- 概要：二段の定数図式を積添字の定数図式へ戻す自然同型（補題 3.2）。
方針：全ての対象に恒等同型を使う。
規約：指定された定数図式関手を使う。使われ方：反復したテンソル増強の終域。 -/
def constantCechUncurryIso :
    (Functor.const K : SSet.{u} ⥤ _) ⋙
        (Functor.whiskeringRight K SSet.{u} (L ⥤ SSet.{u})).obj (Functor.const L) ⋙
          Functor.uncurry ≅ Functor.const (K × L) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Iso.refl X) (by
    intro a b f
    simp)) (by
      intro X Y f
      apply NatTrans.ext
      funext k
      rfl)

/-- 概要：二段の指定重み増強を合成した実際のテンソル増強（論文 補題 3.2）。
方針：外側の増強を内側のテンソルで写し、内側の増強を合成する。
規約：二つの指定比較をそのまま使う。使われ方：反復した錐の指定増強。 -/
def iteratedCechTensorAugmentation : iteratedCechTensor K L W V ⟶ Functor.const (K × L) :=
  Functor.whiskerRight (WeightComparison.tensorComparison K q)
      ((Functor.whiskeringRight K SSet.{u} (L ⥤ SSet.{u})).obj
        (WeightedCones.tensorDiagram L V) ⋙ Functor.uncurry) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (Functor.const K)
        ((Functor.whiskeringRight K SSet.{u} (L ⥤ SSet.{u})).map
          (WeightComparison.tensorComparison L r))) Functor.uncurry ≫
    (constantCechUncurryIso K L).hom

/-- 概要：外重みの増強と二段の増強は指定結合子で可換（補題 3.2）。
方針：各入力と積添字で単位射の結合の恒等式を適用する。
規約：全ての入力空間と図式の射に自然な変換の等式。
使われ方：重みつき Fubini の指定増強の保持。 -/
theorem externalCechTensorIso_augmentation :
    (externalCechTensorIso K L W V).inv ≫
        WeightComparison.tensorComparison (K × L) (externalCechWeightAugmentation K L q r) =
      iteratedCechTensorAugmentation K L W V q r := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext k
  change (α_ X (W.obj k.1) (V.obj k.2)).hom ≫
      (X ◁ ((q.app k.1 ⊗ₘ r.app k.2) ≫ (λ_ (𝟙_ SSet.{u})).hom) ≫ (ρ_ X).hom) =
    ((X ◁ q.app k.1 ≫ (ρ_ X).hom) ▷ V.obj k.2) ≫
      ((X ◁ r.app k.2 ≫ (ρ_ X).hom) ≫ 𝟙 X)
  rw [Category.comp_id]
  exact cechTensorAugmentation_assoc X (W.obj k.1) (V.obj k.2) (q.app k.1) (r.app k.2)

/-- 概要：反復した重みつき錐空間への指定増強（論文 補題 3.2）。
方針：反復テンソル増強と反復した実際の随伴を使う。
規約：外重みの Fubini 同型から逆算して定義しない。使われ方：指定比較を保つ Fubini。 -/
abbrev iteratedWeightedCechAugmentation : cechAugmentedSource (K × L) ⟶
    cechAugmentedDiagram (K × L) ⋙ iteratedCechConeSpace K L W V :=
  cechAdjunctionAugmentation (K × L) (iteratedCechConeAdjunction K L W V)
    (iteratedCechTensorAugmentation K L W V q r)

/-- 概要：指定重みつき Fubini は反復した指定増強と自然に可換（補題 3.2・3.3）。
方針：指定結合子と増強の可換式を、同じ錐の随伴像の保持へ渡す。
規約：増強つき図式の全ての射についての自然変換の等式。
使われ方：実際の導来 Fubini の指定増強の比較。 -/
theorem weightedCechAugmentation_fubini :
    weightedCechAugmentation (K × L) (externalCechWeight K L W V)
        (externalCechWeightAugmentation K L q r) ≫
      Functor.whiskerLeft (cechAugmentedDiagram (K × L)) (weightedCechFubiniIso K L W V).hom =
        iteratedWeightedCechAugmentation K L W V q r := by
  apply NatTrans.ext
  funext A
  have hm := weightedCechFubiniIso_mate K L W V A.left A.right
    ((WeightComparison.tensorComparison (K × L) (externalCechWeightAugmentation K L q r)).app
      A.left ≫ A.hom)
  have ht := congrArg (fun b ↦ b.app A.left) (externalCechTensorIso_augmentation K L W V q r)
  exact hm.trans (congrArg ((iteratedCechConeAdjunction K L W V).homEquiv A.left A.right)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun b ↦ b ≫ A.hom) ht)))

end SerrePositivity.KST.Descent
