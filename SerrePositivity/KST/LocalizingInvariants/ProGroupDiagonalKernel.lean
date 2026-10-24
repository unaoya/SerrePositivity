module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion

/-!
概要：自己 cospan の完全列で、二射影の一方の核を一様な遷移で零化する。
方針：元の射の eventual 核零化で両射影を消し、前次数の像全射性で残る接続像を消す。
規約：零化段を元に依存させない。使われ方：実対角のホモロジー pro 比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision
variable {U Z C X Y : Tower CommGrpCat.{u}}
  (p : LevelHom U Z) (d : LevelHom Z C) (l r : LevelHom C X) (q : LevelHom X Y)
  (hp0 : ∀ n (x : U.obj n), (d.app n).hom ((p.app n).hom x) = 1)
  (hpair : ∀ n (x : C.obj n),
    (l.app n).hom x = 1 ∧ (r.app n).hom x = 1 ↔
      ∃ z : Z.obj n, (d.app n).hom z = x)
  (hqpair : ∀ n (x : C.obj n),
    (q.app n).hom ((l.app n).hom x) = (q.app n).hom ((r.app n).hom x))

include p d r q hp0 hpair hqpair in
lemma eventuallyKernelTrivial_of_pair_exact
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
    (X.transition hmk).hom ((l.app k).hom x) at hlm
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

end SerrePositivity.KST.LocalizingInvariants.ProGroup
