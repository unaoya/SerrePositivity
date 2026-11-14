module

public import SerrePositivity.Archive.KST.DescentConditional.CechAdjointReindex
public import SerrePositivity.KST.Descent.WeightedCechConeCompatibility
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen

/-!
# 添字随伴による実際の重みの移送

## 概要
左随伴な添字変更に対し、右随伴への前合成で重みを移し、実際の重みつき錐を同定する。

## 方針
前合成の実際の随伴と重みつきテンソル随伴を合成し、射影的 cofibrancy は左 Quillen 性から導く。

## 規約
点ごとの cofibrancy を射影的 cofibrancy と同一視しない。指定重みの増強を保持する。

## 使われ方
論文 補題 3.2 の分裂余単体対象の指定比較と添字変更。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.CechReindex

variable {K L : Type u} [SmallCategory K] [SmallCategory L]
  {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b) (W : K ⥤ SSet.{u})

/-- 概要：添字の右随伴に前合成して移した重み（補題 3.2）。
方針：元の全ての重みの射を指定右随伴で制限する。
規約：左随伴への単なる制限とは異なる。使われ方：cofibrant な重みの添字変更。 -/
abbrev weight : L ⥤ SSet.{u} := b ⋙ W

/-- 概要：移した重みのテンソルは元のテンソルの右随伴への前合成（補題 3.2）。
方針：各成分のテンソルと射を定義で比較する。
規約：指定の自然同型を保持。使われ方：重みつき錐の随伴の合成。 -/
def tensorIso : WeightedCones.tensorDiagram L (weight (b := b) W) ≅
    WeightedCones.tensorDiagram K W ⋙ precomp b := Iso.refl _

/-- 概要：移した重みのテンソルの実際の合成随伴（補題 3.2）。
方針：元の重み随伴に添字前合成の随伴を合成する。
規約：上の指定テンソル同型を使う。使われ方：指定重みつき錐の比較。 -/
def coneAdjunction : WeightedCones.tensorDiagram L (weight (b := b) W) ⊣
    precomp a ⋙ WeightedCones.coneSpace K W :=
  ((WeightedCones.adjunction K W).comp (adj.whiskerLeft SSet.{u})).ofNatIsoLeft
    (tensorIso W).symm

/-- 概要：移した重みの実際の錐空間と制限後の錐空間の自然同型（補題 3.2）。
方針：同じ左随伴の実際の二つの随伴を比較する。
規約：合成随伴と同じ指定データを使う。使われ方：指定増強の計算。 -/
def coneIso : WeightedCones.coneSpace L (weight (b := b) W) ≅
    precomp a ⋙ WeightedCones.coneSpace K W :=
  (WeightedCones.adjunction L _).rightAdjointUniq (coneAdjunction adj W)

/-- 概要：指定重みの増強を右随伴で制限（補題 3.2）。
方針：元の自然変換に右随伴を前合成する。
規約：終域は同じ定数単位重み。使われ方：可縮な重みの移送。 -/
def augmentation (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u})) :
    weight (b := b) W ⟶ (Functor.const L).obj (𝟙_ SSet.{u}) := Functor.whiskerLeft b q

section Model

variable [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- 概要：任意の添字前合成は実際の射影的模型間で右 Quillen（補題 3.2）。
方針：fibration と自明 fibration を元の像の各点で検査する。
規約：左クラスを点ごとに判定しない。使われ方：随伴を持つ前合成の左 Quillen 性。 -/
lemma precomp_isRightQuillen (c : K ⥤ L) :
    let := Projective.modelCategory K I J
    let := Projective.modelCategory L I J
    IsRightQuillen (precomp c) := by
  let := Projective.modelCategory K I J
  let := Projective.modelCategory L I J
  exact ⟨fun _ _ _ hf k ↦ hf (c.obj k),
    fun _ _ _ hf ↦ ⟨fun k ↦ hf.1 (c.obj k), fun k ↦ hf.2 (c.obj k)⟩⟩

include adj in
/-- 概要：添字右随伴への前合成は実際の射影的模型間で左 Quillen（補題 3.2）。
方針：指定添字随伴と前合成の右 Quillen 性を使う。
規約：元の添字の随伴から導出。使われ方：移した重みの cofibrancy。 -/
lemma precomp_rightAdjoint_isLeftQuillen :
    let := Projective.modelCategory K I J
    let := Projective.modelCategory L I J
    IsLeftQuillen (precomp b) := by
  let := Projective.modelCategory K I J
  let := Projective.modelCategory L I J
  have := precomp_isRightQuillen I J a
  exact Quillen.isLeftQuillen_of_isRightQuillen (adj.whiskerLeft SSet.{u})

include adj in
/-- 概要：射影的 cofibrant 重みは添字右随伴への前合成で cofibrant（補題 3.2）。
方針：実際の前合成左 Quillen 関手で cofibrant 対象を写す。
規約：点ごとの cofibrancy だけでは結論しない。使われ方：指定重み変更での実降下の移行。 -/
lemma weight_isCofibrant
    (hW : let := Projective.modelCategory K I J; IsCofibrant W) :
    let := Projective.modelCategory L I J
    IsCofibrant (weight (b := b) W) := by
  let := Projective.modelCategory K I J
  let := Projective.modelCategory L I J
  have : IsCofibrant W := hW
  have := precomp_rightAdjoint_isLeftQuillen adj I J
  let : (precomp b).IsLeftAdjoint := (adj.whiskerLeft SSet.{u}).isLeftAdjoint
  exact Quillen.isCofibrant_obj (precomp b) W

end Model
end SerrePositivity.KST.Descent.CechReindex
