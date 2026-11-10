module

public import SerrePositivity.AlgebraicGeometry.BasicOpenFlatCenterGluing
public import SerrePositivity.AlgebraicGeometry.FreeOpenDimensionInduction

/-!
概要：各ファイバーで自由化主開を持つ加群を、一つのアフィン基底中心で平坦化する。
方針：余核に次元帰納を適用した主近傍を有限個選び、中心を貼り合わせる。
規約：正規化先は滑らかで幾何学的整とする。
使われ方：Stacks 0815 の自由化ブローアップの各標準チャートに適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：各ファイバーと交わる自由化主開があれば、より小さい台の次元に関する帰納仮定から基底全体の中心を作れる。
方針：各点で得た局所中心の定義域から有限主開被覆を選び、共通細分を使う。
規約：すべての中心は境界の主開の外に置く。
使われ方：Stacks 0815 の最初のブローアップの一つの標準チャートで平坦化を完了する。
-/
theorem exists_affine_flatPure_center_of_fiber_freeOpens
    {R : CommRingCat.{u}} {B N : Type u} [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite B N]
    (n : ℕ) [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (a : R) (ha : IsRegular a) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] N)]
    (hrec : HasAffineFlatPureCentersBelow.{u} n)
    (hfree : ∀ p : PrimeSpectrum R, ∃ b ∉ p.asIdeal.map (algebraMap R B),
      Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a N := by
  classical
  let good : Set R := {c | let A := CommRingCat.of (Localization.Away c)
    letI : Algebra R A := inferInstanceAs (Algebra R (Localization.Away c))
    ∃ J : Ideal A, PrimeSpectrum.basicOpen (algebraMap R A a) ≤ affineCenterComplement J ∧
      HasFlatPurePullbacks (affineBlowupπ J) (algebraMap R A a) (A ⊗[R] N)}
  have hgood (p : PrimeSpectrum R) : ∃ c ∈ good, c ∉ p.asIdeal := by
    obtain ⟨b, hb, hfree⟩ := hfree p
    let : Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N) := hfree
    obtain ⟨c, hc, J, _, hJ, hflat⟩ :=
      exists_basicOpen_flatPure_center_of_smaller_fibers (N := N) n a ha hrec p b hb
    exact ⟨c, ⟨J, hJ, hflat⟩, hc⟩
  have htop : Ideal.span good = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal (Ideal.span good) h
    obtain ⟨c, hc, hcm⟩ := hgood ⟨m, hm.isPrime⟩
    exact hcm (hsm (Ideal.subset_span hc))
  obtain ⟨s, hsg, hs⟩ := (Ideal.span_eq_top_iff_finite good).mp htop
  let r : s → R := fun i => i.1
  have hr : Ideal.span (Set.range r) = ⊤ := by
    rw [show Set.range r = (↑s : Set R) from Subtype.range_val]
    exact hs
  have hlocal (i : s) := hsg i.2
  choose J hJ hJflat using hlocal
  exact exists_affine_flatPure_center_of_basicOpen_centers r hr a N J hJ hJflat

end SerrePositivity.AlgebraicGeometry
