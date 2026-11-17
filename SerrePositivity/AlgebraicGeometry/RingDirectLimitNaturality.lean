module

public import SerrePositivity.AlgebraicGeometry.RingDirectLimitCocone
public import SerrePositivity.AlgebraicGeometry.RingDirectLimitIntNaturality

/-!
概要：同じ環の順極限と圏論的余極限の標準比較を、環の射に自然にする。
方針：既存の代数的な順極限の射と有限段からの標準写像を使う。
規約：加群への忘却を介さず、元の環準同型を保持する。
使われ方：実際の Frobenius の矢印と conerve の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {A B : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, CommRing (B n)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) (g : ∀ i j, i ≤ j → B i →+* B j)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]
variable (a : ∀ n, A n →+* B n)
variable (ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x))

/-- 実際の可換な環準同型の系を、同じ環の図式の自然変換として読む。 -/
def ringDirectSystemNatTrans : ringDirectSystemFunctor f ⟶ ringDirectSystemFunctor g where
  app n := CommRingCat.ofHom (a n)
  naturality {i j} h := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ha i j (leOfHom h) x

set_option backward.isDefEq.respectTransparency false in
/-- 標準比較は、各有限段の元を同じ余極限の標準写像へ送る。 -/
theorem ringDirectLimitColimitIso_of (n : ℕ) (x : A n) :
    (ringDirectLimitColimitIso f).hom.hom (DirectLimit.Ring.of A f n x) =
      (colimit.ι (ringDirectSystemFunctor f) n).hom x :=
  congrArg (fun k : CommRingCat.of (A n) ⟶ colimit (ringDirectSystemFunctor f) ↦ k.hom x)
    (ringDirectLimitColimitIso_ι f n)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ環の順極限と圏論的余極限の比較は、元の有向系の射に自然。 -/
theorem ringDirectLimitColimitIso_naturality :
    CommRingCat.ofHom (ringDirectLimitComparison f g a ha) ≫
        (ringDirectLimitColimitIso g).hom =
      (ringDirectLimitColimitIso f).hom ≫ colim.map (ringDirectSystemNatTrans f g a ha) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk f z
  change (ringDirectLimitColimitIso g).hom.hom
      (ringDirectLimitComparison f g a ha (DirectLimit.Ring.of A f n x)) =
    (colim.map (ringDirectSystemNatTrans f g a ha)).hom
      ((ringDirectLimitColimitIso f).hom.hom (DirectLimit.Ring.of A f n x))
  rw [ringDirectLimitComparison_of, ringDirectLimitColimitIso_of, ringDirectLimitColimitIso_of]
  exact (congrArg (fun k ↦ k.hom x) (colimit.ι_map (ringDirectSystemNatTrans f g a ha) n)).symm

end SerrePositivity.AlgebraicGeometry
