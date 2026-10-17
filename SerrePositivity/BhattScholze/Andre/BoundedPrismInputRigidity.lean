module

public import SerrePositivity.BhattScholze.Andre.BoundedPrismInputCategory
public import SerrePositivity.BhattScholze.Andre.PerfectPrismBoundedTargetRigidity

/-!
# André A1-a：完全基底上の入力作用からの基底保存性

## 概要

完全基底上の有界入力 prism 間の射では、入力作用を保てば基底射も自動的に保たれる。
BS Lemma 4.8（著者版 pp.38–39）の一意性を Rem 7.15（p.62）の入力圏へ接続する。

## 方針

入力の可換性を係数環へ制限し、完全な基底から有界標的への prism 射の剛性を使う。
原典の変形理論とは異なる幾何和・イデアル冪による一意性の経路。

## 規約

対象は既に基底射を持つものとする。基底射の存在や絶対 site 全体との圏同値は主張しない。

## 使われ方

固定基底上の入力圏から基底射を省く比較における、射の条件の冗長性を解消する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.BoundedPrismInput
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable {W : OrientedPrism p A} {c : A ⧸ W.ideal →+* S}

/-- 概要：完全基底上の有界 prism 射は入力作用を保つなら基底も保つ。
方針：商射の基底制限を一致させ、一般有界標的での完全源の剛性を使う。
規約：標的の完全性・p 正則性は不要。
使われ方：BS Lemma 4.8（著者版 pp.38–39）と Rem 7.15（p.62）の入力圏の比較。 -/
theorem prismHom_over_base_of_input (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) (f : OrientedPrism.Hom X.prism Y.prism)
    (hf : f.quotientMap.comp X.input = Y.input) : f.comp X.base = Y.base := by
  apply perfectPrismHom_ext_to_bounded_target W hW Y.prism Y.bounded
  rw [OrientedPrism.Hom.quotientMap_comp, ← X.input_base,
    ← RingHom.comp_assoc, hf, Y.input_base]

/-- 概要：入力作用だけを保つ prism 射を入力圏の射へまとめる。
方針：完全基底に関する基底保存性を一意性から自動的に供給する。
規約：基底保存性を追加の引数として要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の基底を省く比較射の構成。 -/
def homOfInput (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) (f : OrientedPrism.Hom X.prism Y.prism)
    (hf : f.quotientMap.comp X.input = Y.input) : X ⟶ Y where
  toHom := f
  over_base := prismHom_over_base_of_input hW X Y f hf
  over_input := hf

/-- 概要：入力圏の射は、入力作用を保つ prism 射と型同値。
方針：台の prism 射への射影と基底保存性を自動供給する構成が互いに逆と示す。
規約：対象の基底射の存在は保持し、射の追加基底条件だけを除く。
使われ方：BS Lemma 4.8（著者版 pp.38–39）による絶対入力圏への比較の射の部分。 -/
def homEquivInputPreserving (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) :
    (X ⟶ Y) ≃ { f : OrientedPrism.Hom X.prism Y.prism //
      f.quotientMap.comp X.input = Y.input } where
  toFun f := ⟨f.toHom, f.over_input⟩
  invFun f := homOfInput hW X Y f.val f.property
  left_inv _f := hom_ext rfl
  right_inv _f := Subtype.ext rfl

end SerrePositivity.BhattScholze.Andre.BoundedPrismInput
