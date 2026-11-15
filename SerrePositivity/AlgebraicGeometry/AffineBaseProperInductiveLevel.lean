module

public import SerrePositivity.AlgebraicGeometry.NoetherianProperInductiveLevel
public import SerrePositivity.AlgebraicGeometry.ProperSurjectiveCoefficientModel

/-!
概要：任意の affine 基底上の固有全射に有限の帰納的レベルを供給する。
方針：G2 の実際の固有全射模型に Noether な存在を適用し、Cartesian 比較で戻す。
規約：元の環の Noether 性・模型の存在を仮定しない。
使われ方：G3 の BS17 Lemma 2.6 の affine 基底の場合の出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- BS17 Lemma 2.6 の affine 基底の場合：任意の環上の固有全射には有限の帰納的レベルがある。 -/
theorem exists_properInductiveLevel_affineBase {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [Surjective f] [LocallyOfFinitePresentation f] :
    ∃ n : ℕ, ProperInductiveLevel n f := by
  obtain ⟨A, hA, Y, p, hfp, hp, hs, a, hpb⟩ :=
    exists_proper_surjective_finitePresentation_coefficient_model ℤ R f
  letI : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp hA
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  letI := hfp
  letI := hp
  letI := hs
  obtain ⟨n, hn⟩ := exists_properInductiveLevel_noetherian p
  exact ⟨n, ProperInductiveLevel.of_isPullback hpb hn⟩

end SerrePositivity.AlgebraicGeometry
