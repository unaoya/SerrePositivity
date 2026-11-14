module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import Mathlib.CategoryTheory.Equivalence

/-!
# 入力作用を持つ有界 prism の圏

## 概要
入力作用を持つ有界な向き付き prism の圏と、固定基底上の向きなし有界入力 prism の圏。原典の (R/A)_Δ の対象に S の作用を足したもの。
BS 著者版 Remark 7.15 の根の包を受け取る、有界 prism の入力圏を定める。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Initiality`、`PowerRootEnvelope/InputUniversal`、`Variants/Auxiliary`。
-/

universe u

/-! ## André A1-a：入力作用を持つ有界な向き付き prism の圏

## 概要

固定した基底 prism と入力環に対し、商への入力作用を持つ有界な向き付き prism を対象とし、
基底と入力作用を保つ prism 射を射とする圏を構成する。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope の普遍性を表すための圏。

## 方針

既存の一般の prism 射と標準商射を使い、恒等射・合成の可換性を確認する。
原典の普遍性を補う明示的な圏の実装による経路。

## 規約

各対象の台環は同じ宇宙に置く。orientation 自体の厳密な保存は要求しない。
この圏の構成だけから任意の入力の envelope の存在は結論しない。

## 使われ方

元の H の prism 構造と入力作用が供給されたとき、その初期性と一意な同型を表す。
-/

@[expose] public noncomputable section BoundedPrismInputCategory

namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable (W : OrientedPrism p A) (c : A ⧸ W.ideal →+* S)

/-- 概要：固定した入力環の作用を持つ有界な向き付き基底 prism の対象。
方針：台環・prism・基底射・剰余への入力射とその可換性・有界性を束ねる。
規約：基底の orientation を厳密に保存する条件は追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期対象の舞台。 -/
structure BoundedPrismInput where
  /-- 概要：台の可換環。方針：束ねた環を使う。規約：宇宙を固定。使われ方：BS 著者版 Remark 7.15 p.62 の対象。 -/
  ring : CommRingCat.{u}
  /-- 概要：台環の prism。方針：既存構造を使う。規約：向きを選ぶ。使われ方：BS 著者版 Remark 7.15 p.62 の対象。 -/
  prism : OrientedPrism p ring
  /-- 概要：基底 prism 射。方針：一般の射を使う。規約：イデアルを保つ。使われ方：BS 著者版 Remark 7.15 p.62 の基底。 -/
  base : OrientedPrism.Hom W prism
  /-- 概要：剰余への入力射。方針：実際の商を使う。規約：全元を扱う。使われ方：BS 著者版 Remark 7.15 p.62 の入力。 -/
  input : S →+* ring ⧸ prism.ideal
  /-- 概要：入力と基底の可換性。方針：合成等式。規約：自然な商射。使われ方：BS 著者版 Remark 7.15 p.62 の入力作用。 -/
  input_base : input.comp c = base.quotientMap
  /-- 概要：剰余の有界 p ねじれ。方針：一様指数を指定。規約：零環も許す。使われ方：BS 著者版 Remark 7.15 p.62 の有界性。 -/
  bounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : ring ⧸ prism.ideal,
    (p : ring ⧸ prism.ideal) ^ n * x = 0 → (p : ring ⧸ prism.ideal) ^ N * x = 0

namespace BoundedPrismInput
variable {W c}

/-- 概要：基底と入力作用を保つ有界 prism 間の射。
方針：既存の prism 射と二つの可換図式を束ねる。
規約：台環射と δ・イデアル保存性は親構造から継承する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期性の射。 -/
structure Hom (X Y : BoundedPrismInput W c) extends OrientedPrism.Hom X.prism Y.prism where
  /-- 概要：基底との可換性。方針：prism 射の合成等式。規約：元の基底。使われ方：BS 著者版 Remark 7.15 p.62 の射。 -/
  over_base : toHom.comp X.base = Y.base
  /-- 概要：入力作用との可換性。方針：標準商射の合成等式。規約：全入力元。使われ方：BS 著者版 Remark 7.15 p.62 の射。 -/
  over_input : toHom.quotientMap.comp X.input = Y.input

/-- 概要：入力作用を持つ射は台の prism 射で決まる。
方針：構造の可換性の証明には証明の一意性を使う。
規約：基底と入力環は固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の射の一意性。 -/
@[ext] theorem hom_ext {X Y : BoundedPrismInput W c} {f g : Hom X Y}
    (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- 概要：入力作用を持つ対象の恒等射。
方針：prism の恒等射と商の恒等射を使う。
規約：全入力元を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の圏の恒等射。 -/
def homId (X : BoundedPrismInput W c) : Hom X X where
  toHom := OrientedPrism.Hom.id X.prism
  over_base := OrientedPrism.Hom.id_comp X.base
  over_input := by rw [OrientedPrism.Hom.quotientMap_id, RingHom.id_comp]

/-- 概要：基底と入力作用を保つ射の合成。
方針：prism 射と商射の合成公式で可換性をつなぐ。
規約：引数は圏の合成の順序とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の圏の合成。 -/
def homComp {X Y Z : BoundedPrismInput W c} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := g.toHom.comp f.toHom
  over_base := by rw [OrientedPrism.Hom.comp_assoc, f.over_base, g.over_base]
  over_input := by
    rw [OrientedPrism.Hom.quotientMap_comp, RingHom.comp_assoc, f.over_input, g.over_input]

/-- 概要：入力作用を持つ有界な向き付き prism の圏構造。
方針：恒等射と合成の法則を台の prism 射の法則へ戻す。
規約：対象の存在や初期対象の存在は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の envelope の初期性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の比較射の計算。 -/
theorem id_toHom (X : BoundedPrismInput W c) :
    (𝟙 X : X ⟶ X).toHom = OrientedPrism.Hom.id X.prism := rfl

/-- 概要：圏の合成は台の prism 射の合成。
方針：圏構造の定義を使う。
規約：圏の合成順序を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の比較射の合成。 -/
theorem comp_toHom {X Y Z : BoundedPrismInput W c} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = g.toHom.comp f.toHom := rfl

/-- 概要：基底と入力作用を保つ prism 射の一意存在から圏の初期性を得る。
方針：一意な prism 射を圏の射にまとめ、台の射の一意性を使う。
規約：一意存在は明示引数に要求し、初期対象の存在を無条件に仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的な普遍性から IsInitial への接続。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の envelope 比較を実環の同型として取り出す。 -/
def isoRingEquiv {X Y : BoundedPrismInput W c} (e : X ≅ Y) : X.ring ≃+* Y.ring :=
  { e.hom.toHom.toRingHom with
    invFun := e.inv.toHom.toRingHom
    left_inv := fun x => congrArg (fun h : X ⟶ X => h.toHom.toRingHom x) e.hom_inv_id
    right_inv := fun y => congrArg (fun h : Y ⟶ Y => h.toHom.toRingHom y) e.inv_hom_id }

end BoundedPrismInput
end SerrePositivity.BhattScholze.Andre

end BoundedPrismInputCategory

/-! ## A1-f：固定基底上の向きなし有界入力 prism

## 概要
イデアル J と δ 構造・基底射・入力作用を保持し、独立な生成元をデータとして持たない。
## 方針
J が基底の d の像で生成される条件と、その像の正則性・導来完備性を使う。
## 規約
BS 著者版 Definition 3.2（著者版 pp.28–29）の固定基底上の主イデアルの場合。
一般の可逆イデアルの降下を実装したとはしない。BS 著者版 Proposition 3.13（pp.33–35）は引用しない。
## 使われ方
既存の向き付き入力圏との同値に沿って源の初期性を移す。
-/

@[expose] public noncomputable section Category

namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable (W : OrientedPrism p A) (c : A ⧸ W.ideal →+* S)

/-- 概要：向きを選ばない固定基底上の有界入力 prism。
方針：イデアルを保持し、基底の d の像に関する prism 条件を命題として束ねる。
規約：生成元の独立したデータはなく、正則性は主 Cartier イデアルの条件。
使われ方：固定基底版の向きなし入力圏の対象。 -/
structure BoundedPrismInputUnoriented where
  /-- 概要：台環。方針：可換環を束ねる。規約：宇宙を固定。使われ方：対象の台。 -/
  ring : CommRingCat.{u}
  /-- 概要：δ 構造。方針：既存の構造を使う。規約：素数を固定。使われ方：prism 条件。 -/
  delta : DeltaStructure p ring
  /-- 概要：基底環射。方針：環射を保持。規約：向きは持たない。使われ方：固定基底上の対象。 -/
  base : A →+* ring
  /-- 概要：基底の δ 保存。方針：命題で保持。規約：元の δ 構造。使われ方：基底 prism 射。 -/
  base_delta : W.deltaStructure.IsDeltaHom delta base
  /-- 概要：prism イデアル J。方針：実イデアルを保持。規約：生成元は別に持たない。使われ方：標準商。 -/
  ideal : Ideal ring
  /-- 概要：J=(d)B。方針：イデアル等式を要求。規約：固定基底の d を使用。使われ方：標準的な向き。 -/
  ideal_eq : ideal = Ideal.span {base W.generator}
  /-- 概要：主 Cartier 条件。方針：基底の像の正則性。規約：零環も許す。使われ方：prism 構成。 -/
  regular : Function.Injective (fun x : ring => base W.generator * x)
  /-- 概要：導来 p 完備性。方針：既存の消滅条件。規約：p 正則性は不要。使われ方：prism 構成。 -/
  complete_p : IsModuleComplete ring (p : ring) (ModuleCat.of ring ring)
  /-- 概要：導来 J 完備性。方針：基底の像で表示。規約：独立な向きなし。使われ方：prism 構成。 -/
  complete_d : IsModuleComplete ring (base W.generator) (ModuleCat.of ring ring)
  /-- 概要：prism の包含条件。方針：J と φ(J) を使う。規約：実イデアル。使われ方：BS 著者版 Definition 3.2 の条件。 -/
  p_mem : (p : ring) ∈ ideal ⊔ ideal.map delta.frobeniusLift
  /-- 概要：基底のイデアル保存。方針：包含で保持。規約：生成元の厳密保存は不要。使われ方：商射。 -/
  base_ideal : W.ideal ≤ ideal.comap base
  /-- 概要：剰余への入力作用。方針：実際の商を使う。規約：全入力元。使われ方：envelope の普遍性。 -/
  input : S →+* ring ⧸ ideal
  /-- 概要：入力と基底の可換性。方針：合成等式。規約：標準商射。使われ方：入力圏の対象。 -/
  input_base : input.comp c = Ideal.quotientMap ideal base base_ideal
  /-- 概要：剰余の有界 p ねじれ。方針：一様指数の存在。規約：零環も許す。使われ方：有界性。 -/
  bounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : ring ⧸ ideal,
    (p : ring ⧸ ideal)^n*x = 0 → (p : ring ⧸ ideal)^N*x = 0

namespace BoundedPrismInputUnoriented
variable {W c}

/-- 概要：基底の d の像を用いて標準的な向きを与える。
方針：イデアル等式で prism 条件と入力作用を実際の標準商へ移す。
規約：選択公理で生成元を選び直さない。
使われ方：向き付き入力圏への対象写像。 -/
def orient (X : BoundedPrismInputUnoriented W c) : BoundedPrismInput W c := by
  let Q : OrientedPrism p X.ring :=
    { deltaStructure := X.delta
      generator := X.base W.generator
      generator_regular := X.regular
      complete_p := X.complete_p
      complete_generator := X.complete_d
      p_mem := by
        have h := X.p_mem
        rw [X.ideal_eq, Ideal.map_span, Set.image_singleton,
          ← Ideal.span_union, Set.singleton_union] at h
        exact h }
  have he : X.ideal = Q.ideal := X.ideal_eq
  let e := Ideal.quotEquivOfEq he
  let b : OrientedPrism.Hom W Q :=
    { toRingHom := X.base
      map_delta := X.base_delta
      ideal_le := by rw [← he]; exact X.base_ideal }
  refine
    { ring := X.ring
      prism := Q
      base := b
      input := e.toRingHom.comp X.input
      input_base := ?_
      bounded := ?_ }
  · rw [RingHom.comp_assoc, X.input_base]
    apply Ideal.Quotient.ringHom_ext
    rfl
  · obtain ⟨N, hN⟩ := X.bounded
    refine ⟨N, fun n x hx => ?_⟩
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : (p : X.ring ⧸ X.ideal)^n*y = 0 := by
      apply e.injective
      simpa using hx
    have h := congrArg e (hN n y hy)
    simpa using h

/-- 概要：標準の向きの生成元は基底の d の像。
方針：構成の定義を展開する。規約：生成元の選び直しはない。
使われ方：原典の J=(d)B と向き付き表示の照合。 -/
theorem orient_generator (X : BoundedPrismInputUnoriented W c) :
    (orient X).prism.generator = X.base W.generator := rfl

/-- 概要：標準の向きのイデアルは元の J。
方針：対象のイデアル等式を使う。規約：実際のイデアルを比較する。
使われ方：入力商と prism イデアルの保存。 -/
theorem orient_ideal (X : BoundedPrismInputUnoriented W c) :
    (orient X).prism.ideal = X.ideal := X.ideal_eq.symm

/-- 概要：向きなし対象間の射は δ・基底・入力作用を保つ環射。
方針：標準的な向きを付けた対象間の既存の射を使う。
規約：向きの保存条件は既存の射にもない。
使われ方：向きなし圏の射と合成。 -/
instance category : Category.{u} (BoundedPrismInputUnoriented W c) where
  Hom X Y := orient X ⟶ orient Y
  id X := 𝟙 (orient X)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- 概要：基底の d の像で向きを与える関手。
方針：射の台の環射をそのまま使う。
規約：入力商はイデアル等式で同定済み。
使われ方：圏同値の向き付き側への関手。 -/
def orientFunctor : BoundedPrismInputUnoriented W c ⥤ BoundedPrismInput W c where
  obj := orient
  map f := f

/-- 概要：向き付き対象から生成元の選択を忘れる。
方針：既存の単元倍定理から基底の d の像の正則性とイデアル等式を得る。
規約：基底の完全性も有界標的の完全性も要らない（prism 射の剛性は仮定なし）。
使われ方：忘却関手の対象写像。 -/
def forget (X : BoundedPrismInput W c) : BoundedPrismInputUnoriented W c where
  ring := X.ring
  delta := X.prism.deltaStructure
  base := X.base.toRingHom
  base_delta := X.base.map_delta
  ideal := X.prism.ideal
  ideal_eq := (X.base.span_map_generator).symm
  regular := X.base.map_generator_mul_injective
  complete_p := X.prism.complete_p
  complete_d := X.base.isModuleComplete_map_generator
  p_mem := X.prism.p_mem_sup_map
  base_ideal := X.base.ideal_le
  input := X.input
  input_base := X.input_base
  bounded := X.bounded

/-- 概要：生成元を忘れて基底の像で向きを付け直した対象は元の対象と同型。
方針：同じ台環上の恒等環射を往復に使う。
規約：イデアルの等式による商の移送も入力作用を保つ。
使われ方：忘却関手と圏同値の比較同型。 -/
def orientationIso (X : BoundedPrismInput W c) : orient (forget X) ≅ X := by
  let h : OrientedPrism.Hom (orient (forget X)).prism X.prism :=
    { toRingHom := RingHom.id X.ring
      map_delta := X.prism.deltaStructure.isDeltaHom_id
      ideal_le := by
        change Ideal.span {X.base.toRingHom W.generator} ≤ X.prism.ideal.comap _
        intro x hx
        exact (forget X).ideal_eq.ge hx }
  let k : OrientedPrism.Hom X.prism (orient (forget X)).prism :=
    { toRingHom := RingHom.id X.ring
      map_delta := X.prism.deltaStructure.isDeltaHom_id
      ideal_le := by
        change X.prism.ideal ≤ (Ideal.span {X.base.toRingHom W.generator}).comap _
        intro x hx
        exact (forget X).ideal_eq.le hx }
  refine
    { hom := { toHom := h, over_base := ?_, over_input := ?_ }
      inv := { toHom := k, over_base := ?_, over_input := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply OrientedPrism.Hom.ext; rfl
  · ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (X.input s)
    change h.quotientMap ((orient (forget X)).input s) = X.input s
    change h.quotientMap (Ideal.quotEquivOfEq (forget X).ideal_eq (X.input s)) = X.input s
    rw [← ha]
    rfl
  · apply OrientedPrism.Hom.ext; rfl
  · ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (X.input s)
    change k.quotientMap (X.input s) = (orient (forget X)).input s
    change k.quotientMap (X.input s) = Ideal.quotEquivOfEq (forget X).ideal_eq (X.input s)
    rw [← ha]
    rfl
  · apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl
  · apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl

/-- 概要：向きの選択を忘れる関手。
方針：標準的な向きへの恒等環同型で各射を共役する。
規約：台の環射は元の射と同じ。
使われ方：向きなし対象への初期性の移送。 -/
def forgetFunctor : BoundedPrismInput W c ⥤ BoundedPrismInputUnoriented W c where
  obj := forget
  map {X Y} (f : X ⟶ Y) :=
    (show orient (forget X) ⟶ orient (forget Y) from
      (orientationIso X).hom ≫ f ≫ (orientationIso Y).inv)
  map_id X := by apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl
  map_comp {X Y Z} f g := by
    apply BoundedPrismInput.hom_ext
    apply OrientedPrism.Hom.ext
    rfl

/-- 概要：忘却関手は台の環射を変えない。
方針：比較同型の恒等環射を計算する。規約：基底・入力保存も射に保持される。
使われ方：向きなし初期性で得た射の実環上の照合。 -/
theorem forgetFunctor_map_toRingHom {X Y : BoundedPrismInput W c} (f : X ⟶ Y) :
    ((forgetFunctor).map f).toHom.toRingHom = f.toHom.toRingHom := rfl

/-- 概要：向き付き入力圏と向きなし入力圏の同値。
方針：往復の比較同型はいずれも台環上の恒等環射。
規約：宇宙と固定完全基底・入力作用を保つ。
使われ方：向きに依存しない envelope の普遍性。 -/
def equivalence : BoundedPrismInput W c ≌ BoundedPrismInputUnoriented W c where
  functor := forgetFunctor
  inverse := orientFunctor
  unitIso := NatIso.ofComponents (fun X => (orientationIso X).symm) (by
    intro X Y f
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl)
  counitIso := NatIso.ofComponents (fun X =>
    { hom := (orientationIso (orient X)).hom
      inv := (orientationIso (orient X)).inv
      hom_inv_id := (orientationIso (orient X)).hom_inv_id
      inv_hom_id := (orientationIso (orient X)).inv_hom_id }) (by
    intro X Y f
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl)
  functor_unitIso_comp X := by
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl

end BoundedPrismInputUnoriented
end SerrePositivity.BhattScholze.Andre

end Category
