module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion

/-!
概要：実 pullback の完全列から、射影の eventual 核零化と像全射性を導く。
方針：もう一方の脚の核・像条件と元の対の完全性を共通の遷移段で使う。
規約：元に依存しない零化段を選ぶ。使われ方：一般 cospan 模型の群 pro 比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision
variable {U Z C X Y W : Tower CommGrpCat.{u}}
  (p : LevelHom U Z) (d : LevelHom Z C) (l : LevelHom C W) (r : LevelHom C X) (q : LevelHom X Y) (t : LevelHom W Y)
  (hp0 : ∀ n (x : U.obj n), (d.app n).hom ((p.app n).hom x) = 1)
  (hpair : ∀ n (x : C.obj n),
    (l.app n).hom x = 1 ∧ (r.app n).hom x = 1 ↔
      ∃ z : Z.obj n, (d.app n).hom z = x)
  (hqpair : ∀ n (x : C.obj n),
    (t.app n).hom ((l.app n).hom x) = (q.app n).hom ((r.app n).hom x))

include p d r q t hp0 hpair hqpair in
lemma eventuallyKernelTrivial_of_pullback_pair_exact
    (hp : IsEventuallyImageSurjective p) (hq : IsEventuallyKernelTrivial q) :
    IsEventuallyKernelTrivial l := by
  intro n
  obtain ⟨m, hnm, hm⟩ := hp n
  obtain ⟨k, hmk, hk⟩ := hq m
  refine ⟨k, hnm.trans hmk, fun x hx => ?_⟩
  have hrx : (q.app k).hom ((r.app k).hom x) = 1 := by
    rw [← hqpair, hx, map_one]
  have hlm := congrArg (fun t => t.hom x) (l.naturality hmk)
  have hrm := congrArg (fun t => t.hom x) (r.naturality hmk)
  change (l.app m).hom ((C.transition hmk).hom x) =
    (W.transition hmk).hom ((l.app k).hom x) at hlm
  change (r.app m).hom ((C.transition hmk).hom x) =
    (X.transition hmk).hom ((r.app k).hom x) at hrm
  have hlzero : (l.app m).hom ((C.transition hmk).hom x) = 1 := by
    exact hlm.trans (by rw [hx, map_one])
  have hrzero : (r.app m).hom ((C.transition hmk).hom x) = 1 :=
    hrm.trans (hk _ hrx)
  obtain ⟨z, hz⟩ := (hpair m _).1 ⟨hlzero, hrzero⟩
  obtain ⟨a, ha⟩ := hm z
  have hd := congrArg (fun t => t.hom z) (d.naturality hnm)
  have hzero : (C.transition hnm).hom ((d.app m).hom z) = 1 :=
    hd.symm.trans ((congrArg (d.app n).hom ha.symm).trans (hp0 n a))
  have hc := congrArg (fun t => t.hom x) (C.transition_comp hmk hnm)
  exact hc.symm.trans ((congrArg (C.transition hnm).hom hz.symm).trans hzero)

include r q t in
lemma eventuallyImageSurjective_of_pullback_pair_exact
    (himage : ∀ n (x : X.obj n) (y : W.obj n),
      (q.app n).hom x = (t.app n).hom y →
        ∃ z : C.obj n, (r.app n).hom z = x ∧ (l.app n).hom z = y)
    (hq : IsEventuallyImageSurjective q) : IsEventuallyImageSurjective l := by
  intro n
  obtain ⟨m, hnm, hm⟩ := hq n
  refine ⟨m, hnm, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hm ((t.app m).hom y)
  have ht := congrArg (fun s => s.hom y) (t.naturality hnm)
  change (t.app n).hom ((W.transition hnm).hom y) =
    (Y.transition hnm).hom ((t.app m).hom y) at ht
  obtain ⟨z, _, hz⟩ := himage n x ((W.transition hnm).hom y) (hx.trans ht.symm)
  exact ⟨z, hz⟩

end SerrePositivity.KST.LocalizingInvariants.ProGroup
