module

public import SerrePositivity.Archive.KST.DescentConditional.WeightedCechDerivedConeCompatibility
public import Mathlib.CategoryTheory.Comma.Basic

/-!
# 増強つき単体集合の図式と指定ホモトピー錐

## 概要
増強元・図式・指定増強を同時に動かす圏を用い、指定重みつき錐と実際のホモトピー極限への比較を自然変換にする。

## 方針
定数図式関手の comma 圏に錐の随伴対応を適用し、既存の指定置換比較と合成する。

## 規約
指定増強を関手の射に含める。比較の対象ごとの存在へ弱めず、全ての射への自然性を保持する。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech・分裂降下・細分の指定比較の共通の入口。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K]

/-- 概要：増強元・図式・指定増強を持つ実際の圏（論文 補題 3.2）。
方針：定数図式関手と図式の恒等関手の comma 圏を取る。
規約：K = Δ の場合に余単体図式の指定増強を表す。使われ方：Čech 比較の全自然性。 -/
abbrev AugmentedCechDiagram :=
  Comma (Functor.const K : SSet.{u} ⥤ K ⥤ SSet.{u}) (𝟭 (K ⥤ SSet.{u}))

/-- 概要：指定増強の元の空間への射影（論文 補題 3.2）。
方針：comma の左射影を使う。
規約：射は指定された元の射。使われ方：降下比較の始域関手。 -/
abbrev cechAugmentedSource : AugmentedCechDiagram K ⥤ SSet.{u} := Comma.fst _ _

/-- 概要：指定増強の図式への射影（論文 補題 3.2）。
方針：comma の右射影を使う。
規約：図式の全ての射を保持する。使われ方：降下比較の終域関手。 -/
abbrev cechAugmentedDiagram : AugmentedCechDiagram K ⥤ (K ⥤ SSet.{u}) := Comma.snd _ _

/-- 概要：定数への指定比較を持つ随伴から増強つき図式の比較を自然に構成（補題 3.2）。
方針：指定テンソルの増強と元の増強を合成し、随伴対応を適用する。
規約：増強元と図式の両方に自然。使われ方：単一重み・反復重みの指定比較の共通構成。 -/
def cechAdjunctionAugmentation {T : SSet.{u} ⥤ (K ⥤ SSet.{u})}
    {R : (K ⥤ SSet.{u}) ⥤ SSet.{u}} (adj : T ⊣ R)
    (t : T ⟶ Functor.const K) :
    cechAugmentedSource K ⟶ cechAugmentedDiagram K ⋙ R where
  app A := adj.homEquiv A.left A.right (t.app A.left ≫ A.hom)
  naturality {A B} f := by
    apply adj.homEquiv_naturality_left_square
    have hf : (Functor.const K).map f.left ≫ B.hom = A.hom ≫ f.right := f.w
    change T.map f.left ≫ (t.app B.left ≫ B.hom) = (t.app A.left ≫ A.hom) ≫ f.right
    rw [← Category.assoc, t.naturality f.left, Category.assoc, hf, ← Category.assoc]

/-- 概要：指定増強を指定重みの実際の錐空間へ送る自然変換（補題 3.2）。
方針：重み増強と元の増強を合成し、実際の随伴対応を適用する。
規約：増強元と図式を同時に変える全ての射に自然。
使われ方：実際のホモトピー極限への指定 Čech 比較。 -/
def weightedCechAugmentation (W : K ⥤ SSet.{u})
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u})) :
    cechAugmentedSource K ⟶ cechAugmentedDiagram K ⋙ WeightedCones.coneSpace K W :=
  cechAdjunctionAugmentation K (WeightedCones.adjunction K W)
    (WeightComparison.tensorComparison K q)

variable [ModelCategory SSet.{u}] (I J : MorphismProperty SSet.{u})
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：指定増強を実際の置換込みの重みつき計算へ送る自然変換（補題 3.2）。
方針：指定錐の随伴像を既存の指定置換比較で写す。
規約：重みを変更する前の実際の計算。使われ方：増強を保つ導来重み変更。 -/
def computedWeightedCechAugmentation (W : K ⥤ SSet.{u})
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u})) :
    cechAugmentedSource K ⟶
      cechAugmentedDiagram K ⋙ CofibrantCechWeight.weightedFunctor K I J W :=
  weightedCechAugmentation K W q ≫ Functor.whiskerLeft (cechAugmentedDiagram K)
    (CofibrantCechWeight.weightedComparison K I J W)

/-- 概要：指定増強から既存の実際のホモトピー極限への自然変換（補題 3.2・3.3）。
方針：選択された cofibrant 重みと指定増強を使い、実際の fibrant 置換後へ送る。
規約：通常の極限を使わず、指定比較を固定する。
使われ方：実際の Čech 降下の主張の指定写像。 -/
abbrev homotopyCechAugmentation : cechAugmentedSource K ⟶
    cechAugmentedDiagram K ⋙ HomotopyCones.functor K I J :=
  computedWeightedCechAugmentation K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weightComparison K I J)

/-- 概要：実際の指定増強比較が弱同値であるという降下条件（補題 3.2・3.3）。
方針：構成した指定写像に模型の弱同値を課す。
規約：降下の結論を証明や追加公理にはしない。使われ方：transfer の retract・分裂・細分の比較。 -/
def HasCechSpaceDescent (A : AugmentedCechDiagram K) : Prop :=
  weakEquivalences SSet.{u} ((homotopyCechAugmentation K I J).app A)

end SerrePositivity.KST.Descent
