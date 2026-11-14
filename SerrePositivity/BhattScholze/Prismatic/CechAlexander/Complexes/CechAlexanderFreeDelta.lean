module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.CechAlexanderEnvelopeData

/-!
# Čech の添字による完備自由 δ 環の射

## 概要
単体射による変数の添字の写像を、完備自由 δ 環の射へ一意に延長する。

## 方針
既存の完備自由 δ 環の普遍性と射の外延性を使う。

## 規約
BS 著者版 Construction 4.18。包絡の選択に依存しない始域の構造射。

## 使われ方
一般の包絡の余単体的構造と後の底変換の比較の入力。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-- 単体射は各元の添字を保ち、頂点だけを送る。 -/
@[expose] def cechIndexMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : cechIndex R m → cechIndex R n :=
  fun s => (s.1, θ.toOrderHom s.2)

private theorem existsUnique_cechFreeDeltaMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃! g : cechFreeDelta P R m →+* cechFreeDelta P R n,
      (completedFreeDeltaStructure P _).IsDeltaHom (completedFreeDeltaStructure P _) g ∧
      g.comp (completedFreeDeltaBase P _) = completedFreeDeltaBase P _ ∧
      ∀ s, g (completedFreeDeltaVariable P _ s) =
        completedFreeDeltaVariable P _ (cechIndexMap R θ s) :=
  existsUnique_completedFreeDeltaHom P _ (completedFreeDeltaStructure P _)
    (completedFreeDeltaBase P _) (completedFreeDeltaBase_isDeltaHom P _)
    (completedFreeDelta_complete_p P _) (completedFreeDelta_complete_generator P _)
    (fun s => completedFreeDeltaVariable P _ (cechIndexMap R θ s))

/-- 概要：単体射を完備自由 δ 環へ延長した射。
方針：変数の添字の写像を既存の普遍性で延長する。
規約：BS 著者版 Construction 4.18。使われ方：包絡の始域の余単体的構造。 -/
def cechFreeDeltaMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    cechFreeDelta P R m →+* cechFreeDelta P R n :=
  (existsUnique_cechFreeDeltaMap P R θ).choose

/-- 単体射による延長は δ 射。 -/
theorem cechFreeDeltaMap_isDeltaHom {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (completedFreeDeltaStructure P _).IsDeltaHom (completedFreeDeltaStructure P _)
      (cechFreeDeltaMap P R θ) :=
  (existsUnique_cechFreeDeltaMap P R θ).choose_spec.1.1

/-- 単体射による延長は基底を保つ。 -/
theorem cechFreeDeltaMap_base {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (cechFreeDeltaMap P R θ).comp (completedFreeDeltaBase P _) = completedFreeDeltaBase P _ :=
  (existsUnique_cechFreeDeltaMap P R θ).choose_spec.1.2.1

/-- 単体射による延長は指定した変数をその添字の変数へ送る。 -/
theorem cechFreeDeltaMap_variable {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : cechIndex R m) :
    cechFreeDeltaMap P R θ (completedFreeDeltaVariable P _ s) =
      completedFreeDeltaVariable P _ (cechIndexMap R θ s) :=
  (existsUnique_cechFreeDeltaMap P R θ).choose_spec.1.2.2 s

/-- 恒等単体射の延長は恒等環射。 -/
theorem cechFreeDeltaMap_id (n : ℕ) : cechFreeDeltaMap P R (𝟙 ⦋n⦌) = RingHom.id _ := by
  apply completedFreeDeltaHom_ext P _ (completedFreeDeltaStructure P _)
    (completedFreeDeltaBase P _) (completedFreeDeltaBase_isDeltaHom P _)
    (completedFreeDelta_complete_p P _) (completedFreeDelta_complete_generator P _)
    (cechFreeDeltaMap_isDeltaHom P R _) (DeltaStructure.isDeltaHom_id _)
  · exact cechFreeDeltaMap_base P R _
  · rfl
  · intro s
    exact cechFreeDeltaMap_variable P R _ s

/-- 単体射の合成の延長は延長の合成。 -/
theorem cechFreeDeltaMap_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (τ : ⦋m⦌ ⟶ ⦋n⦌) :
    cechFreeDeltaMap P R (θ ≫ τ) = (cechFreeDeltaMap P R τ).comp (cechFreeDeltaMap P R θ) := by
  apply completedFreeDeltaHom_ext P _ (completedFreeDeltaStructure P _)
    (completedFreeDeltaBase P _) (completedFreeDeltaBase_isDeltaHom P _)
    (completedFreeDelta_complete_p P _) (completedFreeDelta_complete_generator P _)
    (cechFreeDeltaMap_isDeltaHom P R _)
    ((cechFreeDeltaMap_isDeltaHom P R τ).comp (cechFreeDeltaMap_isDeltaHom P R θ))
  · exact cechFreeDeltaMap_base P R _
  · rw [RingHom.comp_assoc, cechFreeDeltaMap_base, cechFreeDeltaMap_base]
  · intro s
    rw [RingHom.comp_apply, cechFreeDeltaMap_variable, cechFreeDeltaMap_variable,
      cechFreeDeltaMap_variable]
    rfl

end SerrePositivity.BhattScholze.Prismatic
