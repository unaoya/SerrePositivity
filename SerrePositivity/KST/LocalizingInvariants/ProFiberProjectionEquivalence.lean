module

public import SerrePositivity.KST.LocalizingInvariants.ProFiberConnecting
public import SerrePositivity.KST.LocalizingInvariants.ProFiberZero
public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion

/-!
概要：実 fiber 図式の塔の左項が全整数 π-pro 零なら、元の射影は π-pro 同値である。
方針：自然な接続レベル射と段ごとの四項完全性を、可換群の pro 同型判定へ渡す。
規約：一般 pro ∞ 圏の同値性は主張しない。使われ方：Tor pro 消滅から抽象切除。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

variable (D : ProFiberSequence.{u}) (hF : ProSpectrum.IsPiProZero (vertex D 0 0))

include hF in
lemma groupProjection_isProIso_succ (j : ℤ) :
    ProExcision.IsProIso (groupProjection D (j + 1)) :=
  ProGroup.proIso_of_fourTerm_exact_proZero (groupInclusion D (j + 1))
    (groupProjection D (j + 1)) (connectingHom D j)
    (fun n x ↦ exact_total D n (j + 1) x) (fun n x ↦ exact_base D n j x)
    (hF (j + 1)) (hF j)

include hF in
lemma projection_piProEquivalence : ProSpectrum.IsPiProEquivalence (projection D) := by
  intro j
  have he : j - 1 + 1 = j := by omega
  have hp := groupProjection_isProIso_succ D hF (j - 1)
  rw [he] at hp
  exact hp

end SerrePositivity.KST.LocalizingInvariants.ProFiberSequence
