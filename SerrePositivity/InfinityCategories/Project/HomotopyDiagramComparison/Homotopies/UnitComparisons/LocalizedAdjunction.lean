module

public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# 局所化前の自然な Hom 同型から局所化圏上の随伴へ

概要：Hovey §1.3 の導来 Hom の自然同型を普通の局所化圏上の随伴へ降ろす。
方針：局所化による前合成の充満忠実性を二つの変数に順に適用する。
規約：元の圏の随伴やモデル構造の存在は要求しない。
使われ方：定値 E 代数図式と具体的な極限計算関手の導来随伴。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD uH uJ w

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

open CategoryTheory Opposite

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {H : Type uH} [Category.{w} H] {J : Type uJ} [Category.{w} J]

/-- 概要：随伴の左辺の Hom 二変数関手（Hovey §1.3）。
方針：左関手の反対化の後に同じ coyoneda を使う。
規約：始域に反変、終域に共変。
使われ方：局所化による前合成から復元する Hom 関手。 -/
abbrev leftHom (F : H ⥤ J) : Hᵒᵖ ⥤ J ⥤ Type w := F.op ⋙ coyoneda

/-- 概要：随伴の右辺の Hom 二変数関手（Hovey §1.3）。
方針：coyoneda の終域へ右関手を前合成する。
規約：同じ Hom 宇宙を使う。
使われ方：局所化後の Hom の同値の右辺。 -/
abbrev rightHom (G : J ⥤ H) : Hᵒᵖ ⥤ J ⥤ Type w :=
  coyoneda ⋙ (Functor.whiskeringLeft J H (Type w)).obj G

/-- 概要：Hom 二変数関手を二つの局所化の手前へ制限する（Hovey §1.3）。
方針：始域の反対化と終域の局所化へ前合成する。
規約：元の射の局所化像をそのまま使う。
使われ方：具体的な導来 Hom 同値の自然性の入力。 -/
abbrev restrict (Q : C ⥤ H) (R : D ⥤ J) (T : Hᵒᵖ ⥤ J ⥤ Type w) :
    Cᵒᵖ ⥤ D ⥤ Type w := Q.op ⋙ T ⋙ (Functor.whiskeringLeft D J (Type w)).obj R

variable (Q : C ⥤ H) (W : MorphismProperty C) [Q.IsLocalization W]
  (R : D ⥤ J) (V : MorphismProperty D) [R.IsLocalization V]
  (F : H ⥤ J) (G : J ⥤ H)

/-- 概要：制限した Hom 同型は局所化圏全体で一意に復元できる（Hovey §1.3）。
方針：終域の局所化の充満忠実性、続いて始域の反対局所化の充満忠実性を使う。
規約：モデル構造や元の随伴は不要。
使われ方：実際の局所化圏上の Hom 同型の構成。 -/
def descendHomIso (e : restrict Q R (leftHom F) ≅ restrict Q R (rightHom G)) :
    leftHom F ≅ rightHom G := by
  let hR := Localization.fullyFaithfulWhiskeringLeft R V (Type w)
  let e' := (hR.whiskeringRight Cᵒᵖ).preimageIso
    (X := Q.op ⋙ leftHom F) (Y := Q.op ⋙ rightHom G) e
  let hQ := Localization.fullyFaithfulWhiskeringLeft Q.op W.op (J ⥤ Type w)
  exact hQ.preimageIso (X := leftHom F) (Y := rightHom G) e'

/-- 概要：降ろした Hom 同型は元の局所化像で同じ成分を持つ（Hovey §1.3）。
方針：二つの充満忠実な前合成の preimage の計算式を順に評価する。
規約：任意の局所化像の両変数で元の同型を保持する。
使われ方：構成した随伴と元の導来 Hom 同値の照合。 -/
lemma descendHomIso_hom_app
    (e : restrict Q R (leftHom F) ≅ restrict Q R (rightHom G)) (X : C) (Y : D) :
    ((descendHomIso Q W R V F G e).hom.app (op (Q.obj X))).app (R.obj Y) =
      (e.hom.app (op X)).app Y := by
  let hR := Localization.fullyFaithfulWhiskeringLeft R V (Type w)
  let hS := hR.whiskeringRight Cᵒᵖ
  let e' := hS.preimageIso (X := Q.op ⋙ leftHom F) (Y := Q.op ⋙ rightHom G) e
  let hQ := Localization.fullyFaithfulWhiskeringLeft Q.op W.op (J ⥤ Type w)
  have h₁ := congr_app (hQ.map_preimage e'.hom) (op X)
  have h₂ := congr_app (congr_app (hS.map_preimage
    (X := Q.op ⋙ leftHom F) (Y := Q.op ⋙ rightHom G) e.hom) (op X)) Y
  exact (congr_app h₁ (R.obj Y)).trans h₂

/-- 概要：Hom 二変数関手の同型は実際の随伴を与える（Hovey §1.3）。
方針：逆の始域自然性と順方向の終域自然性を Hom 随伴の構成へ移す。
規約：二変数関手の同じ成分を Hom 同値として使う。
使われ方：降ろした導来 Hom の同型を随伴へ束ねる。 -/
def adjunctionOfHomIso (e : leftHom F ≅ rightHom G) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => ((e.app (op X)).app Y).toEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        exact ConcreteCategory.congr_hom (congr_app (e.inv.naturality f.op) Y) g
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact ConcreteCategory.congr_hom ((e.hom.app (op X)).naturality g) f }

/-- 概要：元の両変数に自然な導来 Hom 同型から局所化圏上の随伴を構成（Hovey §1.3）。
方針：同じ Hom 同型を二つの局所化から復元して Hom 随伴へ束ねる。
規約：元の圏での随伴を入力仮定にしない。
使われ方：具体的な極限計算関手と定値図式の導来随伴。 -/
def descendAdjunction (e : restrict Q R (leftHom F) ≅ restrict Q R (rightHom G)) : F ⊣ G :=
  adjunctionOfHomIso F G (descendHomIso Q W R V F G e)

/-- 概要：構成した随伴の Hom 同値は制限した元の Hom 同型（Hovey §1.3）。
方針：Hom 随伴の構成の計算式と二つの充満忠実な前合成の成分式を使う。
規約：任意の局所化像の両対象で同じ関数を回収する。
使われ方：具体的な導来 Hom の同値と随伴の正規化。 -/
lemma descendAdjunction_homEquiv_app
    (e : restrict Q R (leftHom F) ≅ restrict Q R (rightHom G)) (X : C) (Y : D)
    (x : F.obj (Q.obj X) ⟶ R.obj Y) :
    (descendAdjunction Q W R V F G e).homEquiv (Q.obj X) (R.obj Y) x =
      ((e.hom.app (op X)).app Y) x := by
  simp only [descendAdjunction, adjunctionOfHomIso, Adjunction.mkOfHomEquiv_homEquiv]
  exact ConcreteCategory.congr_hom (descendHomIso_hom_app Q W R V F G e X Y) x

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
