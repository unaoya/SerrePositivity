module

public import SerrePositivity.BhattScholze.Andre.Unoriented.Category
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicSourceInitiality

/-!
# A1-f：向きなし入力圏での元の源の初期性

## 概要
A1-a の正次数モニック源の初期性を向きなし入力圏へ移す。
## 方針
圏同値の恒等環射による比較同型と、既存の初期性を使う。
## 規約
固定完全基底と同じ宇宙の対象に限る。元の H と完備入力の作用を変更しない。
## 使われ方
BS Rem 7.15（著者版 p.62）の向きに依存しない普遍性を公開する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable {W : OrientedPrism p A} {c : A ⧸ W.ideal →+* S}

/-- 概要：向き付き入力対象の初期性は向きなし対象へ移る。
方針：同値の比較同型で源を移し、射の一意性をそのまま使う。
規約：任意の入力対象に適用でき、完全性は固定基底だけに要求する。
使われ方：元の源の向きなし初期性への共通接続。 -/
def BoundedPrismInput.initial_unoriented (hW : W.deltaStructure.IsPerfect)
    (X : BoundedPrismInput W c) (hX : IsInitial X) :
    IsInitial (BoundedPrismInputUnoriented.forget hW X) := by
  have hi := hX.ofIso (BoundedPrismInputUnoriented.orientationIso hW X).symm
  apply IsInitial.ofUniqueHom (fun Y => hi.to (BoundedPrismInputUnoriented.orient Y))
  intro Y f
  exact hi.hom_ext _ _

/-- 概要：元の正次数モニック源は向きなし有界入力 prism の圏で初期。
方針：A1-a の証明済みの初期性を、向きを忘れる関手に沿って移す。
規約：正則性・有界性の追加仮定はなく、元の台環・δ・基底・入力を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の固定完全基底での向きなし envelope。 -/
def powerRootPrismMonicSourceInput_initial_unoriented
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsInitial (BoundedPrismInputUnoriented.forget hW
      (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)) :=
  BoundedPrismInput.initial_unoriented hW _
    (powerRootPrismMonicSourceInput_isInitialOfMonicPositive W hW f hf hdeg)

end SerrePositivity.BhattScholze.Andre
