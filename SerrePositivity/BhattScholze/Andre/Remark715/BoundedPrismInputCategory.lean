module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# André A1-a：入力作用を持つ有界な向き付き prism の圏

## 概要

固定した基底 prism と入力環に対し、商への入力作用を持つ有界な向き付き prism を対象とし、
基底と入力作用を保つ prism 射を射とする圏を構成する。
BS Rem 7.15（著者版 p.62）の絶対 envelope の普遍性を表すための圏。

## 方針

既存の一般の prism 射と標準商射を使い、恒等射・合成の可換性を確認する。
原典の普遍性を補う明示的な圏の実装による経路。

## 規約

各対象の台環は同じ宇宙に置く。orientation 自体の厳密な保存は要求しない。
この圏の構成だけから任意の入力の envelope の存在は結論しない。

## 使われ方

元の H の prism 構造と入力作用が供給されたとき、その初期性と一意な同型を表す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable (W : OrientedPrism p A) (c : A ⧸ W.ideal →+* S)

/-- 概要：固定した入力環の作用を持つ有界な向き付き基底 prism の対象。
方針：台環・prism・基底射・剰余への入力射とその可換性・有界性を束ねる。
規約：基底の orientation を厳密に保存する条件は追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の初期対象の舞台。 -/
structure BoundedPrismInput where
  /-- 概要：台の可換環。方針：束ねた環を使う。規約：宇宙を固定。使われ方：Rem 7.15 p.62 の対象。 -/
  ring : CommRingCat.{u}
  /-- 概要：台環の prism。方針：既存構造を使う。規約：向きを選ぶ。使われ方：Rem 7.15 p.62 の対象。 -/
  prism : OrientedPrism p ring
  /-- 概要：基底 prism 射。方針：一般の射を使う。規約：イデアルを保つ。使われ方：Rem 7.15 p.62 の基底。 -/
  base : OrientedPrism.Hom W prism
  /-- 概要：剰余への入力射。方針：実際の商を使う。規約：全元を扱う。使われ方：Rem 7.15 p.62 の入力。 -/
  input : S →+* ring ⧸ prism.ideal
  /-- 概要：入力と基底の可換性。方針：合成等式。規約：自然な商射。使われ方：Rem 7.15 p.62 の入力作用。 -/
  input_base : input.comp c = base.quotientMap
  /-- 概要：剰余の有界 p ねじれ。方針：一様指数を指定。規約：零環も許す。使われ方：Rem 7.15 p.62 の有界性。 -/
  bounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : ring ⧸ prism.ideal,
    (p : ring ⧸ prism.ideal) ^ n * x = 0 → (p : ring ⧸ prism.ideal) ^ N * x = 0

namespace BoundedPrismInput
variable {W c}

/-- 概要：基底と入力作用を保つ有界 prism 間の射。
方針：既存の prism 射と二つの可換図式を束ねる。
規約：台環射と δ・イデアル保存性は親構造から継承する。
使われ方：BS Rem 7.15（著者版 p.62）の初期性の射。 -/
structure Hom (X Y : BoundedPrismInput W c) extends OrientedPrism.Hom X.prism Y.prism where
  /-- 概要：基底との可換性。方針：prism 射の合成等式。規約：元の基底。使われ方：Rem 7.15 p.62 の射。 -/
  over_base : toHom.comp X.base = Y.base
  /-- 概要：入力作用との可換性。方針：標準商射の合成等式。規約：全入力元。使われ方：Rem 7.15 p.62 の射。 -/
  over_input : toHom.quotientMap.comp X.input = Y.input

/-- 概要：入力作用を持つ射は台の prism 射で決まる。
方針：構造の可換性の証明には証明の一意性を使う。
規約：基底と入力環は固定する。
使われ方：BS Rem 7.15（著者版 p.62）の射の一意性。 -/
@[ext] theorem hom_ext {X Y : BoundedPrismInput W c} {f g : Hom X Y}
    (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- 概要：入力作用を持つ対象の恒等射。
方針：prism の恒等射と商の恒等射を使う。
規約：全入力元を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の圏の恒等射。 -/
def homId (X : BoundedPrismInput W c) : Hom X X where
  toHom := OrientedPrism.Hom.id X.prism
  over_base := OrientedPrism.Hom.id_comp X.base
  over_input := by rw [OrientedPrism.Hom.quotientMap_id, RingHom.id_comp]

/-- 概要：基底と入力作用を保つ射の合成。
方針：prism 射と商射の合成公式で可換性をつなぐ。
規約：引数は圏の合成の順序とする。
使われ方：BS Rem 7.15（著者版 p.62）の圏の合成。 -/
def homComp {X Y Z : BoundedPrismInput W c} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := g.toHom.comp f.toHom
  over_base := by rw [OrientedPrism.Hom.comp_assoc, f.over_base, g.over_base]
  over_input := by
    rw [OrientedPrism.Hom.quotientMap_comp, RingHom.comp_assoc, f.over_input, g.over_input]

/-- 概要：入力作用を持つ有界な向き付き prism の圏構造。
方針：恒等射と合成の法則を台の prism 射の法則へ戻す。
規約：対象の存在や初期対象の存在は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の envelope の初期性。 -/
instance category : Category.{u} (BoundedPrismInput W c) where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp f := hom_ext (OrientedPrism.Hom.comp_id f.toHom)
  comp_id f := hom_ext (OrientedPrism.Hom.id_comp f.toHom)
  assoc f g h := hom_ext (OrientedPrism.Hom.comp_assoc h.toHom g.toHom f.toHom).symm

/-- 概要：圏の恒等射の台の prism 射は元の恒等射。
方針：圏構造の定義を使う。
規約：入力対象を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の比較射の計算。 -/
theorem id_toHom (X : BoundedPrismInput W c) :
    (𝟙 X : X ⟶ X).toHom = OrientedPrism.Hom.id X.prism := rfl

/-- 概要：圏の合成は台の prism 射の合成。
方針：圏構造の定義を使う。
規約：圏の合成順序を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の比較射の合成。 -/
theorem comp_toHom {X Y Z : BoundedPrismInput W c} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = g.toHom.comp f.toHom := rfl

/-- 概要：基底と入力作用を保つ prism 射の一意存在から圏の初期性を得る。
方針：一意な prism 射を圏の射にまとめ、台の射の一意性を使う。
規約：一意存在は明示引数に要求し、初期対象の存在を無条件に仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的な普遍性から IsInitial への接続。 -/
def isInitialOfPrismUniversal (X : BoundedPrismInput W c)
    (h : ∀ Y : BoundedPrismInput W c,
      ∃! f : OrientedPrism.Hom X.prism Y.prism,
        f.comp X.base = Y.base ∧ f.quotientMap.comp X.input = Y.input) : IsInitial X := by
  let lift (Y : BoundedPrismInput W c) : X ⟶ Y :=
    { toHom := (h Y).choose
      over_base := (h Y).choose_spec.1.1
      over_input := (h Y).choose_spec.1.2 }
  apply IsInitial.ofUniqueHom lift
  intro Y f
  apply hom_ext
  exact (h Y).choose_spec.2 f.toHom ⟨f.over_base, f.over_input⟩

/-- 概要：入力 prism の圏の同型から台環の環同型を得る。
方針：同型の往復の prism 射を環射に戻し、合成の恒等式を各元で確認する。
規約：基底・入力作用・δ 構造の保存は元の圏の射のデータとして保持される。
使われ方：BS Rem 7.15（著者版 p.62）の envelope 比較を実環の同型として取り出す。 -/
def isoRingEquiv {X Y : BoundedPrismInput W c} (e : X ≅ Y) : X.ring ≃+* Y.ring :=
  { e.hom.toHom.toRingHom with
    invFun := e.inv.toHom.toRingHom
    left_inv := fun x => congrArg (fun h : X ⟶ X => h.toHom.toRingHom x) e.hom_inv_id
    right_inv := fun y => congrArg (fun h : Y ⟶ Y => h.toHom.toRingHom y) e.inv_hom_id }

end BoundedPrismInput
end SerrePositivity.BhattScholze.Andre
