module
public import SerrePositivity.DifferentialGraded.Resolution.BoundaryCells
public import SerrePositivity.DifferentialGraded.Complexes.FilteredCycles

/-! # 境界cellを各後続段階で埋める列の準同型判定

## 概要
dg圏のcell列が構成された後、各Homに適用する具体的な判定。
列・cell充填・余極限の存在を公理として導入しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ComplexBoundaryCell
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]
variable (F : ℕ ⥤ Complex A) (s a : Cocone F) (hs : IsColimit s)

/-- 全有限段のcellを次段階で埋めれば、余極限でも全cellが埋まる。
transitionの次数ごとの単射性も、増大射の全射性も不要。 -/
lemma sequential_filling
    (h : ∀ (k : ℕ) (c : ComplexBoundaryCell A (a.ι.app k)),
      ∃ t : (F.obj (k + 1)).X c.degree,
        (F.obj (k + 1)).d c.degree (c.degree + 1) t =
          (F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) c.cycle.val ∧
        (a.ι.app (k + 1)).f c.degree t = c.primitive)
    (c : ComplexBoundaryCell A (hs.desc a)) : c.HasFilling A := by
  obtain ⟨k, z, hz⟩ := complexSequentialColimit_cycle_rep A F s hs (c.degree + 1) c.cycle
  have hb : a.pt.d c.degree (c.degree + 1) c.primitive =
      (a.ι.app k).f (c.degree + 1) z.val := by
    have hf := congrArg (fun f => f.f (c.degree + 1) z.val) (hs.fac a k)
    change (hs.desc a).f (c.degree + 1) ((s.ι.app k).f (c.degree + 1) z.val) =
      (a.ι.app k).f (c.degree + 1) z.val at hf
    exact c.boundary.trans ((congrArg ((hs.desc a).f (c.degree + 1)) hz.symm).trans hf)
  let ck : ComplexBoundaryCell A (a.ι.app k) := ⟨c.degree, z, c.primitive, hb⟩
  obtain ⟨t, ht, hp⟩ := h k ck
  refine ⟨(s.ι.app (k + 1)).f c.degree t, ?_, ?_⟩
  · have hd := congrArg (fun f => f t) ((s.ι.app (k + 1)).comm c.degree (c.degree + 1))
    change s.pt.d c.degree (c.degree + 1) ((s.ι.app (k + 1)).f c.degree t) =
      (s.ι.app (k + 1)).f (c.degree + 1) ((F.obj (k + 1)).d c.degree (c.degree + 1) t) at hd
    have hw := congrArg (fun f => f.f (c.degree + 1) z.val)
      (s.w (homOfLE (Nat.le_succ k)))
    change (s.ι.app (k + 1)).f (c.degree + 1)
      ((F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) z.val) =
      (s.ι.app k).f (c.degree + 1) z.val at hw
    exact hd.trans ((congrArg ((s.ι.app (k + 1)).f (c.degree + 1)) ht).trans (hw.trans hz))
  · have hf := congrArg (fun f => f.f c.degree t) (hs.fac a (k + 1))
    change (hs.desc a).f c.degree ((s.ι.app (k + 1)).f c.degree t) =
      (a.ι.app (k + 1)).f c.degree t at hf
    exact hf.trans hp

lemma sequential_quasiIso
    (h : ∀ (k : ℕ) (c : ComplexBoundaryCell A (a.ι.app k)),
      ∃ t : (F.obj (k + 1)).X c.degree,
        (F.obj (k + 1)).d c.degree (c.degree + 1) t =
          (F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) c.cycle.val ∧
        (a.ι.app (k + 1)).f c.degree t = c.primitive) : QuasiIso (hs.desc a) :=
  quasiIso_of_filling A (sequential_filling A F s a hs h)

end SerrePositivity.DifferentialGraded.ComplexBoundaryCell
