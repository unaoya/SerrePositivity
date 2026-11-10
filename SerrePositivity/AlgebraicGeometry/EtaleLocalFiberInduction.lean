module

public import SerrePositivity.AlgebraicGeometry.FiniteNormalizationFlatCenter
public import SerrePositivity.AlgebraicGeometry.RelativeNormalizationAffineRings

/-!
概要：有限型アフィン始域の各点で、次元帰納から étale 局所の平坦化中心を得る。
方針：各点の相対 Noether 正規化で、滑らかな正規化先に有限押し出しを適用する。
規約：ファイバー環の次元の上限は一様な自然数とする。
使われ方：零化イデアルで切り出した台の étale 被覆に中心をそろえる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/--
概要：小さい次元に関する平坦化の帰納仮定は、より大きい上限から導ける。
方針：ファイバー台の次元の不等式を合成する。
規約：境界や加群の条件は共通。
使われ方：各正規化先の相対次元が異なる場合に、同じ帰納仮定を使う。
-/
theorem HasAffineFlatPureCentersBelow.mono {n m : ℕ} (h : (n : WithBot ℕ∞) ≤ m)
    (hm : HasAffineFlatPureCentersBelow.{u} m) : HasAffineFlatPureCentersBelow.{u} n := by
  intro R _ B N _ _ _ _ _ _ _ _ a ha hflat hd
  exact hm R B N a ha hflat (fun p => (hd p).trans h)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一様なファイバー次元上限を持つ有限型始域の各点は、帰納で平坦化できる étale 局所模型へ持ち上がる。
方針：その点の相対正規化を選び、有限押し出しで局所の平坦化中心を得る。
規約：中心は境界の主開の外にあり、始域と局所基底の四角形の可換性も出力する。
使われ方：各点の局所中心を有限個選び、共通の基底中心に降下する。
-/
theorem exists_etale_local_flatPure_center_at
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [Algebra R B] [Algebra.FiniteType R B]
    {M : Type u} [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Finite B M] (a : R) (ha : IsRegular a)
    [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)]
    (d : ℕ) (hd : ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber B) ≤ d)
    (hrec : HasAffineFlatPureCentersBelow.{u} d) (q : PrimeSpectrum B) :
    ∃ (C D : CommRingCat.{u}) (e : R ⟶ C) (j : B ⟶ D) (g : C ⟶ D)
      (q' : PrimeSpectrum D), e.hom.Etale ∧ j.hom.Etale ∧
      q'.comap j.hom = q ∧ e ≫ g = CommRingCat.ofHom (algebraMap R B) ≫ j ∧
      letI : Algebra B D := j.hom.toAlgebra
      letI : Algebra C D := g.hom.toAlgebra
      ∃ I : Ideal C, I.FG ∧ PrimeSpectrum.basicOpen (e.hom a) ≤ affineCenterComplement I ∧
        HasFlatPurePullbacks (affineBlowupπ I) (e.hom a) (D ⊗[B] M) := by
  obtain ⟨n, hn, C, E, D, e, f, h, j, q', he, hj, hh, hsm, hgi, hq, hcomp⟩ :=
    exists_affine_ring_normalization_at R B q d hd
  exact ⟨C, D, e, j, f ≫ h, q', he, hj, hq, hcomp,
    exists_affine_flatPure_center_of_finite_normalization e f h j hcomp he hj hh n hsm hgi (M := M)
      a ha (hrec.mono hn)⟩

end SerrePositivity.AlgebraicGeometry
