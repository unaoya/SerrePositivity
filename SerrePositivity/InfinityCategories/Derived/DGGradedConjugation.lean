module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutIntervalAlgebra
public import SerrePositivity.InfinityCategories.DGNerve.Residual
/-!
概要：斉次 shift の閉射による境界原始元の前後合成と、二合成の次数・符号を照合する。
方針：同じ Leibniz 式、実単位則と半自由分解のホモトピー逆を使う。
規約：全 Hom の実 cochain を保持する。使われ方：一般 Morita の全高次 Hom の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateBoundary {x y : D} (s : ℤ)
    (f : GradedHom R x y (-s)) (g : GradedHom R y x s)
    (hf : differential R f = 0) (hg : differential R g = 0)
    (h : GradedHom R y y (-1)) :
    differential R (s.negOnePow • compose R (n := (-1 : ℤ)) g
      (compose R (n := -s - 1) h f (by omega)) (by omega)) =
      compose R (n := (0 : ℤ)) g
        (compose R (n := (-s - 1) + 1) (differential R h) f (by omega)) (by omega) := by
  rw [differential_units_smul, differential_compose, hg, zero_compose, zero_add,
    smul_smul, Int.units_mul_self, one_smul, differential_compose, hf,
    compose_zero, smul_zero, add_zero]

/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateBoundary_sub_unit {x y : D} (s : ℤ)
    (f : GradedHom R x y (-s)) (g : GradedHom R y x s)
    (hf : differential R f = 0) (hg : differential R g = 0)
    (hgf : compose R g f (neg_add_cancel s) = (unitElement R x).val)
    (h : GradedHom R y y (-1)) (u : GradedHom R y y 0)
    (hu : (homObject R D y y).d (-1) 0 h = u - (unitElement R y).val) :
    differential R (s.negOnePow • compose R (n := (-1 : ℤ)) g
      (compose R (n := -s - 1) h f (by omega)) (by omega)) =
      compose R (n := (0 : ℤ)) g (compose R (n := (-s - 1) + 1) u f (by omega)) (by omega) -
        (unitElement R x).val := by
  change differential R h = (u - (unitElement R y).val : GradedHom R y y 0) at hu
  rw [dgGradedConjugateBoundary R D s f g hf hg h, hu, compose_sub_left, compose_sub_right]
  refine congrArg₂ (· - ·) rfl ?_
  calc
    _ = compose R (n := (0 : ℤ)) (compose R (n := s) g (unitElement R y).val (by omega)) f
        (neg_add_cancel s) :=
      dgNerveGradedCompose_assoc R D f (unitElement R y).val g (by omega) (by omega) (by omega)
        (neg_add_cancel s)
    _ = _ := by rw [compose_unit, hgf]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateComposite {x y z : D} (s : ℤ)
    (f : GradedHom R x y (-s)) (g : GradedHom R y x s)
    (π : GradedHom R z y 0) (σ : GradedHom R y z 0) :
    compose R (n := (0 : ℤ)) g
      (compose R (n := (-s - 1) + 1)
        (compose R (n := (0 : ℤ)) π σ (by omega)) f (by omega)) (by omega) =
      compose R (n := (0 : ℤ)) (compose R (n := s) g π (by omega))
        (compose R (n := -s) σ f (add_zero _)) (neg_add_cancel s) := by
  calc
    _ = compose R (n := (0 : ℤ))
        (compose R (n := s) g (compose R (n := (0 : ℤ)) π σ (by omega)) (by omega))
        f (neg_add_cancel s) :=
      dgNerveGradedCompose_assoc R D f (compose R (n := (0 : ℤ)) π σ (by omega)) g
        (by omega) (by omega) (by omega)
        (neg_add_cancel s)
    _ = compose R (n := (0 : ℤ))
        (compose R (n := s) (compose R (n := s) g π (by omega)) σ (by omega))
        f (neg_add_cancel s) := by
      congr 1
      exact dgNerveGradedCompose_assoc R D σ π g (by omega) (by omega) (by omega) (by omega)
    _ = _ := (dgNerveGradedCompose_assoc R D f σ (compose R (n := s) g π (by omega))
      (add_zero _) (by omega) (neg_add_cancel s) (neg_add_cancel s)).symm
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedTransferInverseComposite {x y z : D} (s : ℤ)
    (f : GradedHom R x y (-s)) (g : GradedHom R y x s)
    (hfg : compose R f g (add_neg_cancel s) = (unitElement R y).val)
    (π : GradedHom R z y 0) (σ : GradedHom R y z 0) :
    compose R (n := (0 : ℤ)) (compose R (n := -s) σ f (add_zero _))
      (compose R (n := s) g π (by omega)) (add_neg_cancel s) =
        compose R (n := (0 : ℤ)) σ π (by omega) := by
  calc
    _ = compose R (n := (0 : ℤ))
        (compose R (n := (0 : ℤ)) (compose R (n := -s) σ f (add_zero _)) g
          (add_neg_cancel s)) π (by omega) :=
      dgNerveGradedCompose_assoc R D π g (compose R (n := -s) σ f (add_zero _))
        (by omega) (add_neg_cancel s) (add_neg_cancel s) (by omega)
    _ = compose R (n := (0 : ℤ))
        (compose R (n := (0 : ℤ)) σ (compose R f g (add_neg_cancel s)) (by omega))
        π (by omega) := by
      congr 1
      exact (dgNerveGradedCompose_assoc R D g f σ (add_neg_cancel s) (add_zero _)
        (by omega) (add_neg_cancel s)).symm
    _ = _ := by rw [hfg, compose_unit]

end SerrePositivity.InfinityCategories
