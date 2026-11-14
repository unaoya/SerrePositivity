module

public import SerrePositivity.Archive.KST.DescentConditional.CechReindexWeights
public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechSpaces

/-!
# 添字随伴による重み変更と指定増強

## 概要
左随伴な添字変更による実際の重みつき錐の同型が、元の指定増強を保つことを証明する。

## 方針
合成随伴の Hom 対応を成分で計算し、指定重み増強の添字随伴の単位についての自然性を使う。

## 規約
増強を同型の逆で定義しない。両方の指定増強から可換式を証明する。

## 使われ方
論文 補題 3.2 の分裂 Čech の元の指定比較への移行。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent.CechReindex

variable {K L : Type u} [SmallCategory K] [SmallCategory L]
  {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b) (W : K ⥤ SSet.{u})

/-- 概要：添字前合成は指定増強も保持する実際の関手（補題 3.2）。
方針：増強元を固定し、図式と増強に同じ添字関手を前合成する。
規約：comma の可換式を元の射から導く。使われ方：元の Čech への制限。 -/
def augmentedRestriction (c : K ⥤ L) : AugmentedCechDiagram L ⥤ AugmentedCechDiagram K where
  obj A :=
    { left := A.left
      right := c ⋙ A.right
      hom := Functor.whiskerLeft c A.hom }
  map f :=
    { left := f.left
      right := Functor.whiskerLeft c f.right
      w := by
        apply NatTrans.ext
        funext k
        exact congrArg (fun t ↦ t.app (c.obj k)) f.w }
  map_id _ := by apply CommaMorphism.ext <;> rfl
  map_comp _ _ := by apply CommaMorphism.ext <;> rfl

/-- 概要：前合成の随伴の Hom 対応の指定成分（補題 3.2）。
方針：持ち上げた随伴の単位と Hom の単位公式を成分で計算する。
規約：元の添字随伴の単位を使う。使われ方：指定テンソル増強の自然性の適用。 -/
theorem whiskerLeft_homEquiv_app {T : K ⥤ SSet.{u}} {F : L ⥤ SSet.{u}}
    (f : b ⋙ T ⟶ F) (k : K) :
    ((adj.whiskerLeft SSet.{u}).homEquiv T F f).app k =
      T.map (adj.unit.app k) ≫ f.app (a.obj k) := by
  change ((adj.whiskerLeft SSet.{u}).unit.app T).app k ≫ f.app (a.obj k) = _
  rw [Adjunction.whiskerLeft_unit_app_app]

/-- 概要：移した重みの増強の合成随伴像は元の指定増強の制限の随伴像（補題 3.2）。
方針：添字随伴の単位についての指定テンソル増強の自然性を使う。
規約：両方の指定重み増強を保持。使われ方：実際の錐同型と指定比較の整合性。 -/
theorem coneAdjunction_augmentation_mate
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram L) :
    (coneAdjunction adj W).homEquiv A.left A.right
      ((WeightComparison.tensorComparison L (augmentation W q)).app A.left ≫ A.hom) =
    (WeightedCones.adjunction K W).homEquiv A.left (a ⋙ A.right)
      ((WeightComparison.tensorComparison K q).app A.left ≫ Functor.whiskerLeft a A.hom) := by
  rw [coneAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  apply congrArg ((WeightedCones.adjunction K W).homEquiv A.left (a ⋙ A.right))
  apply NatTrans.ext
  funext k
  rw [whiskerLeft_homEquiv_app]
  change ((WeightedCones.tensorDiagram K W).obj A.left).map (adj.unit.app k) ≫
      (((WeightComparison.tensorComparison K q).app A.left).app (b.obj (a.obj k)) ≫
        A.hom.app (a.obj k)) =
      ((WeightComparison.tensorComparison K q).app A.left).app k ≫ A.hom.app (a.obj k)
  have ht := ((WeightComparison.tensorComparison K q).app A.left).naturality (adj.unit.app k)
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ A.hom.app (a.obj k)) (ht.trans (Category.comp_id _)))

/-- 概要：移した重みの実際の錐同型は元の指定増強を保持（補題 3.2）。
方針：同じ左随伴の指定 Hom 対応を右随伴の一意同型で比較する。
規約：同型から増強を逆定義しない。使われ方：実際のホモトピー比較への移行。 -/
theorem coneIso_augmentation
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram L) :
    (weightedCechAugmentation L (weight (b := b) W) (augmentation W q)).app A ≫
        (coneIso adj W).hom.app A.right =
      (weightedCechAugmentation K W q).app ((augmentedRestriction a).obj A) :=
  (cechConeMate_rightAdjointUniq (WeightedCones.adjunction L _)
    (coneAdjunction adj W) _).trans (coneAdjunction_augmentation_mate adj W q A)

end SerrePositivity.KST.Descent.CechReindex
