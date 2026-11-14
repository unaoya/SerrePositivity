module

public import SerrePositivity.AlgebraicGeometry.ProperFinitePresentationCoefficientModel
public import Mathlib.Algebra.Field.ZMod

/-!
概要：一般の固有係数模型を有限型 F_p 上の実際の模型に特殊化する。
方針：F_p の Noether 性と、部分代数の有限生成性と有限型性の同値を使う。
規約：元の環 R の Noether 性を要求しない。
使われ方：B01 の有限型 F_p 上の固有模型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 一般の固有・有限表示射の、有限型 F_p 上の実際の固有模型。 -/
theorem exists_primeField_proper_coefficient_model (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] [Algebra (ZMod p) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [IsProper f] :
    ∃ (A : Subalgebra (ZMod p) R), A.FG ∧ Algebra.FiniteType (ZMod p) A ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of A)),
        LocallyOfFinitePresentation q ∧ IsProper q ∧
        ∃ a : X ⟶ Y, IsPullback a f q (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨A, hA, Y, q, hfp, hq, a, hpb⟩ := exists_proper_finitePresentation_coefficient_model (ZMod p) R f
  exact ⟨A, hA, (Subalgebra.fg_iff_finiteType A).mp hA, Y, q, hfp, hq, a, hpb⟩

end SerrePositivity.AlgebraicGeometry
