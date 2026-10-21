module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupExactZero

/-!
概要：五項完全列の中央の塔が pro 零となる、外側二射の核・像判定を証明する。
方針：右側の eventual 核零化で中央の元を接続射から持ち上げ、左側の像全射性で消す。
規約：同じ遷移と自然なレベル射を保持。使われ方：fiber の次数範囲付き π-pro 判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision

lemma proZero_of_fiveTerm_exact {A B C D E : Tower CommGrpCat.{u}}
    (p : LevelHom A B) (d : LevelHom B C) (i : LevelHom C D) (q : LevelHom D E)
    (hB : ∀ n (x : B.obj n), (d.app n).hom x = 1 ↔
      ∃ y : A.obj n, (p.app n).hom y = x)
    (hC : ∀ n (x : C.obj n), (i.app n).hom x = 1 ↔
      ∃ y : B.obj n, (d.app n).hom y = x)
    (hD : ∀ n (x : D.obj n), (q.app n).hom x = 1 ↔
      ∃ y : C.obj n, (i.app n).hom y = x)
    (hp : IsEventuallyImageSurjective p) (hq : IsEventuallyKernelTrivial q) :
    IsProZero C := by
  intro n
  obtain ⟨m, hnm, hm⟩ := hp n
  obtain ⟨k, hmk, hk⟩ := hq m
  refine ⟨k, hnm.trans hmk, ?_⟩
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  rw [zero_apply]
  have hqx : (q.app k).hom ((i.app k).hom x) = 1 :=
    (hD k _).2 ⟨x, rfl⟩
  have hix := congrArg (fun f ↦ f.hom x) (i.naturality hmk)
  change (i.app m).hom ((C.transition hmk).hom x) =
    (D.transition hmk).hom ((i.app k).hom x) at hix
  obtain ⟨y, hy⟩ := (hC m _).1 (hix.trans (hk _ hqx))
  obtain ⟨z, hz⟩ := hm y
  have hd := congrArg (fun f ↦ f.hom y) (d.naturality hnm)
  change (d.app n).hom ((B.transition hnm).hom y) =
    (C.transition hnm).hom ((d.app m).hom y) at hd
  have hz' : (d.app n).hom ((B.transition hnm).hom y) = 1 :=
    (hB n _).2 ⟨z, hz⟩
  have hc := congrArg (fun f ↦ f.hom x) (C.transition_comp hmk hnm)
  exact hc.symm.trans ((congrArg (C.transition hnm).hom hy.symm).trans
    (hd.symm.trans hz'))

end SerrePositivity.KST.LocalizingInvariants.ProGroup
