module

public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechRows

/-!
# 各行の増強元が変わる二重増強 Čech 図式

## 概要
外側の増強と、外側の各段で異なる増強元を持つ行の関手を保持し、積添字の指定増強を構成する。

## 方針
行の増強つき図式の圏への関手とその増強元への外側増強を comma 圏に保持し、uncurry する。

## 規約
各行の増強元を全体の増強元と同一視しない。curry/uncurry の比較には指定同型を保持する。

## 使われ方
論文 補題 3.2・3.3 の各行の降下と外側の降下から二重 Čech の降下を得る段階。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L]

/-- 概要：外側の増強と増強元が変わる各行を持つ実際の圏（補題 3.2）。
方針：行の増強元へ外側から写す comma 圏を取る。
規約：行は AugmentedCechDiagram L への実際の関手。使われ方：二方向の降下の貼り合わせ。 -/
abbrev DoubleAugmentedCechDiagram := Comma
  (Functor.const K : SSet.{u} ⥤ K ⥤ SSet.{u})
  ((Functor.whiskeringRight K (AugmentedCechDiagram L) SSet.{u}).obj (cechAugmentedSource L))

namespace DoubleAugmentedCechDiagram

variable (A : DoubleAugmentedCechDiagram K L)

/-- 概要：各行の増強元の列への外側の指定増強（補題 3.2）。
方針：元の外側増強をそのまま保持する。
規約：各段の増強元は行の左成分。使われ方：外側の降下の入力。 -/
abbrev outer : AugmentedCechDiagram K := {
  left := A.left
  right := A.right ⋙ cechAugmentedSource L
  hom := A.hom }

/-- 概要：二重増強から積添字の指定増強を構成（補題 3.2）。
方針：外側増強を内側で定数化し、各行の指定増強を合成して uncurry する。
規約：二段の定数図式の指定同型を使用する。使われ方：積添字の実際の降下。 -/
abbrev flatten : AugmentedCechDiagram (K × L) := {
  left := A.left
  right := Functor.uncurry.obj (A.right ⋙ cechAugmentedDiagram L)
  hom := (constantCechUncurryIso K L).inv.app A.left ≫
    Functor.uncurry.map (Functor.whiskerRight A.hom (Functor.const L) ≫
      Functor.whiskerLeft A.right
        (Comma.natTrans (Functor.const L) (𝟭 (L ⥤ SSet.{u})))) }

/-- 概要：積添字の指定増強の各成分は二段の指定増強の合成（補題 3.2）。
方針：定数図式の指定同型の恒等成分を評価する。
規約：同じ増強元と射を保持する。使われ方：各行との指定比較。 -/
theorem flatten_hom_app (k : K) (l : L) :
    (flatten K L A).hom.app (k, l) = A.hom.app k ≫ (A.right.obj k).hom.app l := by
  change 𝟙 A.left ≫ (A.hom.app k ≫ (A.right.obj k).hom.app l) = _
  exact Category.id_comp _

/-- 概要：元の行の図式と積添字化を戻した行の図式の指定同型（補題 3.2）。
方針：curry/uncurry の指定同値の単位同型を使う。
規約：各行の図式を定義上同じと仮定しない。使われ方：行の指定増強の保持。 -/
abbrev curryIso : A.right ⋙ cechAugmentedDiagram L ≅ Functor.curry.obj (flatten K L A).right :=
  (Functor.currying (C := K) (D := L) (E := SSet.{u})).unitIso.app _

/-- 概要：全体の増強元で増強した行から元の行への指定射（補題 3.2）。
方針：左辺に外側増強、右辺に curry/uncurry の指定同型の逆を使う。
規約：行の増強元は変わる。使われ方：実際の行の比較の因子化。 -/
def rowComparison (k : K) : (augmentedCechRows K L (flatten K L A)).obj k ⟶ A.right.obj k where
  left := A.hom.app k
  right := (curryIso K L A).inv.app k
  w := by
    apply NatTrans.ext
    funext l
    change A.hom.app k ≫ (A.right.obj k).hom.app l =
      (flatten K L A).hom.app (k, l) ≫ 𝟙 ((A.right.obj k).right.obj l)
    rw [flatten_hom_app]
    exact (Category.comp_id _).symm

variable [ModelCategory SSet.{u}] (I J : MorphismProperty SSet.{u})
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：積添字の各行の実際の比較は外側増強と元の各行の比較へ因子化（補題 3.2）。
方針：各行への指定 comma 射に既存のホモトピー比較の自然性を適用する。
規約：curry/uncurry の指定同型を保持した自然変換の等式。
使われ方：各行の降下から外側の点ごとの弱同値を得る。 -/
theorem homotopyRowsFactorization :
    rowHomotopyCechAugmentation K L I J (flatten K L A) ≫
        Functor.whiskerRight (curryIso K L A).inv (HomotopyCones.functor L I J) =
      A.hom ≫ Functor.whiskerLeft A.right (homotopyCechAugmentation L I J) := by
  apply NatTrans.ext
  funext k
  exact ((homotopyCechAugmentation L I J).naturality (rowComparison K L A k)).symm

end DoubleAugmentedCechDiagram

end SerrePositivity.KST.Descent
