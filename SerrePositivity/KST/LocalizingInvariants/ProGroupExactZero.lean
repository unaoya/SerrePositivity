module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupKernel

/-!
概要：可換群の塔の完全列における右 pro 零性と両端 pro 零性の効果。
方針：二つの自然性の四角形と完全性を使い、元に依存しない二段の遷移を選ぶ。
規約：一般 pro 圏を構成しない。使われ方：pro fiber 列の零性と同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision
variable {A B C : Tower CommGrpCat.{u}} (i : LevelHom A B) (p : LevelHom B C)
  (hex : ∀ n (x : B.obj n), (p.app n).hom x = 1 ↔ ∃ y : A.obj n, (i.app n).hom y = x)

include p hex in
lemma eventuallyImageSurjective_of_exact_proZero (hC : IsProZero C) :
    IsEventuallyImageSurjective i := by
  intro n
  obtain ⟨m, h, hz⟩ := hC n
  refine ⟨m, h, fun y => ?_⟩
  apply (hex n ((B.transition h).hom y)).1
  have hp := congrArg (fun t => t.hom y) (p.naturality h)
  change (p.app n).hom ((B.transition h).hom y) =
    (C.transition h).hom ((p.app m).hom y) at hp
  rw [hz, zero_apply] at hp
  exact hp

include i p hex in
lemma proZero_of_exact (hA : IsProZero A) (hC : IsProZero C) : IsProZero B := by
  intro n
  obtain ⟨m, hnm, hzA⟩ := hA n
  obtain ⟨k, hmk, hzC⟩ := hC m
  refine ⟨k, hnm.trans hmk, ?_⟩
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  rw [zero_apply]
  have hp := congrArg (fun t => t.hom x) (p.naturality hmk)
  change (p.app m).hom ((B.transition hmk).hom x) =
    (C.transition hmk).hom ((p.app k).hom x) at hp
  rw [hzC, zero_apply] at hp
  obtain ⟨y, hy⟩ := (hex m ((B.transition hmk).hom x)).1 hp
  have hi := congrArg (fun t => t.hom y) (i.naturality hnm)
  change (i.app n).hom ((A.transition hnm).hom y) =
    (B.transition hnm).hom ((i.app m).hom y) at hi
  rw [hzA, zero_apply, map_one, hy] at hi
  have hb := congrArg (fun t => t.hom x) (B.transition_comp hmk hnm)
  exact hb.symm.trans hi.symm

end SerrePositivity.KST.LocalizingInvariants.ProGroup
