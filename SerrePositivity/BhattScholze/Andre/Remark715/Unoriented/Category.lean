module

public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismInputCategory
public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismHomRigidity
public import Mathlib.CategoryTheory.Equivalence

/-!
# A1-f：固定基底上の向きなし有界入力 prism

## 概要
イデアル J と δ 構造・基底射・入力作用を保持し、独立な生成元をデータとして持たない。
## 方針
J が基底の d の像で生成される条件と、その像の正則性・導来完備性を使う。
## 規約
BS Def 3.2（著者版 pp.28–29）の固定基底上の主イデアルの場合。
一般の可逆イデアルの降下を実装したとはしない。Prop 3.13（pp.33–35）は引用しない。
## 使われ方
既存の向き付き入力圏との同値に沿って源の初期性を移す。
-/

@[expose] public noncomputable section
universe u
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
  /-- 概要：prism の包含条件。方針：J と φ(J) を使う。規約：実イデアル。使われ方：Def 3.2 の条件。 -/
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

variable (hW : W.deltaStructure.IsPerfect)

/-- 概要：向き付き対象から生成元の選択を忘れる。
方針：既存の単元倍定理から基底の d の像の正則性とイデアル等式を得る。
規約：完全性は基底だけに要求し、有界標的の完全性は不要。
使われ方：忘却関手の対象写像。 -/
def forget (X : BoundedPrismInput W c) : BoundedPrismInputUnoriented W c where
  ring := X.ring
  delta := X.prism.deltaStructure
  base := X.base.toRingHom
  base_delta := X.base.map_delta
  ideal := X.prism.ideal
  ideal_eq := (boundedPrismHom_generator_span X.base (W.isDistinguished_of_perfect hW)
    X.bounded).symm
  regular := boundedPrismHom_generator_regular X.base (W.isDistinguished_of_perfect hW)
    X.bounded
  complete_p := X.prism.complete_p
  complete_d := boundedPrismHom_generator_complete X.base (W.isDistinguished_of_perfect hW)
    X.bounded
  p_mem := X.prism.p_mem_sup_map
  base_ideal := X.base.ideal_le
  input := X.input
  input_base := X.input_base
  bounded := X.bounded

/-- 概要：生成元を忘れて基底の像で向きを付け直した対象は元の対象と同型。
方針：同じ台環上の恒等環射を往復に使う。
規約：イデアルの等式による商の移送も入力作用を保つ。
使われ方：忘却関手と圏同値の比較同型。 -/
def orientationIso (X : BoundedPrismInput W c) : orient (forget hW X) ≅ X := by
  let h : OrientedPrism.Hom (orient (forget hW X)).prism X.prism :=
    { toRingHom := RingHom.id X.ring
      map_delta := X.prism.deltaStructure.isDeltaHom_id
      ideal_le := by
        change Ideal.span {X.base.toRingHom W.generator} ≤ X.prism.ideal.comap _
        intro x hx
        exact (forget hW X).ideal_eq.ge hx }
  let k : OrientedPrism.Hom X.prism (orient (forget hW X)).prism :=
    { toRingHom := RingHom.id X.ring
      map_delta := X.prism.deltaStructure.isDeltaHom_id
      ideal_le := by
        change X.prism.ideal ≤ (Ideal.span {X.base.toRingHom W.generator}).comap _
        intro x hx
        exact (forget hW X).ideal_eq.le hx }
  refine
    { hom := { toHom := h, over_base := ?_, over_input := ?_ }
      inv := { toHom := k, over_base := ?_, over_input := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply OrientedPrism.Hom.ext; rfl
  · ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (X.input s)
    change h.quotientMap ((orient (forget hW X)).input s) = X.input s
    change h.quotientMap (Ideal.quotEquivOfEq (forget hW X).ideal_eq (X.input s)) = X.input s
    rw [← ha]
    rfl
  · apply OrientedPrism.Hom.ext; rfl
  · ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (X.input s)
    change k.quotientMap (X.input s) = (orient (forget hW X)).input s
    change k.quotientMap (X.input s) = Ideal.quotEquivOfEq (forget hW X).ideal_eq (X.input s)
    rw [← ha]
    rfl
  · apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl
  · apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl

/-- 概要：向きの選択を忘れる関手。
方針：標準的な向きへの恒等環同型で各射を共役する。
規約：台の環射は元の射と同じ。
使われ方：向きなし対象への初期性の移送。 -/
def forgetFunctor : BoundedPrismInput W c ⥤ BoundedPrismInputUnoriented W c where
  obj := forget hW
  map {X Y} (f : X ⟶ Y) :=
    (show orient (forget hW X) ⟶ orient (forget hW Y) from
      (orientationIso hW X).hom ≫ f ≫ (orientationIso hW Y).inv)
  map_id X := by apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl
  map_comp {X Y Z} f g := by
    apply BoundedPrismInput.hom_ext
    apply OrientedPrism.Hom.ext
    rfl

/-- 概要：忘却関手は台の環射を変えない。
方針：比較同型の恒等環射を計算する。規約：基底・入力保存も射に保持される。
使われ方：向きなし初期性で得た射の実環上の照合。 -/
theorem forgetFunctor_map_toRingHom {X Y : BoundedPrismInput W c} (f : X ⟶ Y) :
    ((forgetFunctor hW).map f).toHom.toRingHom = f.toHom.toRingHom := rfl

/-- 概要：向き付き入力圏と向きなし入力圏の同値。
方針：往復の比較同型はいずれも台環上の恒等環射。
規約：宇宙と固定完全基底・入力作用を保つ。
使われ方：向きに依存しない envelope の普遍性。 -/
def equivalence : BoundedPrismInput W c ≌ BoundedPrismInputUnoriented W c where
  functor := forgetFunctor hW
  inverse := orientFunctor
  unitIso := NatIso.ofComponents (fun X => (orientationIso hW X).symm) (by
    intro X Y f
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl)
  counitIso := NatIso.ofComponents (fun X =>
    { hom := (orientationIso hW (orient X)).hom
      inv := (orientationIso hW (orient X)).inv
      hom_inv_id := (orientationIso hW (orient X)).hom_inv_id
      inv_hom_id := (orientationIso hW (orient X)).inv_hom_id }) (by
    intro X Y f
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl)
  functor_unitIso_comp X := by
    apply BoundedPrismInput.hom_ext; apply OrientedPrism.Hom.ext; rfl

end BoundedPrismInputUnoriented
end SerrePositivity.BhattScholze.Andre
