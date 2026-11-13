module

public import SerrePositivity.AlgebraicGeometry.RingDirectLimitIntColimit

/-!
概要：環の順極限と整数加群の余極限の比較を、有向系の環の射に自然にする。
方針：同じ有限段の代表元で両方の写像を照合する。
規約：環の順極限の射を実際の環準同型として構成する。
使われ方：F6 の標準開の制限と閉厚化への射を、係数図式の余極限へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {A B : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, CommRing (B n)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable (g : ∀ i j, i ≤ j → B i →+* B j)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]
variable (a : ∀ n, A n →+* B n)
variable (ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x))

/-- 可換な環の射の系から誘導する、実際の環の順極限の射。 -/
def ringDirectLimitComparison : DirectLimit A f →+* DirectLimit B g :=
  DirectLimit.Ring.lift A f _
    (fun n ↦ (DirectLimit.Ring.of B g n).comp (a n)) (by
      intro i j h x
      change DirectLimit.Ring.of B g j (a j (f i j h x)) = _
      rw [ha]
      exact DirectLimit.Ring.of_f h (a i x))

/-- 環の順極限の射は各有限段で指定した環の射に一致する。 -/
theorem ringDirectLimitComparison_of (n : ℕ) (x : A n) :
    ringDirectLimitComparison f g a ha (DirectLimit.Ring.of A f n x) =
      DirectLimit.Ring.of B g n (a n x) := rfl

/-- 環の順極限と整数加群の余極限の比較は、有向系の環の射に自然。 -/
theorem ringDirectLimitIntColimitIso_naturality :
    ModuleCat.ofHom (ringDirectLimitComparison f g a ha).toAddMonoidHom.toIntLinearMap ≫
        (ringDirectLimitIntColimitIso g).hom =
      (ringDirectLimitIntColimitIso f).hom ≫
        colim.map (linearDirectSystemNatTrans (ringDirectSystemIntMap f)
          (ringDirectSystemIntMap g) (fun n ↦ (a n).toAddMonoidHom.toIntLinearMap) ha) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk f z
  change (ringDirectLimitIntColimitIso g).hom.hom
      (ringDirectLimitComparison f g a ha (DirectLimit.Ring.of A f n x)) =
    (colim.map (linearDirectSystemNatTrans (ringDirectSystemIntMap f)
      (ringDirectSystemIntMap g) (fun n ↦ (a n).toAddMonoidHom.toIntLinearMap) ha)).hom
      ((ringDirectLimitIntColimitIso f).hom.hom (DirectLimit.Ring.of A f n x))
  rw [ringDirectLimitComparison_of, ringDirectLimitIntColimitIso_of,
    ringDirectLimitIntColimitIso_of]
  exact (congrArg (fun k ↦ k.hom x)
    (colimit.ι_map (linearDirectSystemNatTrans (ringDirectSystemIntMap f)
      (ringDirectSystemIntMap g) (fun n ↦ (a n).toAddMonoidHom.toIntLinearMap) ha) n)).symm

end SerrePositivity.AlgebraicGeometry
