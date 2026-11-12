module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutIntervalAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateBoundary {x y : D} (s : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y x s)
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R y y (-1)) :
    _root_.SerrePositivity.DifferentialGraded.differential R (s.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (n := (-1 : ℤ)) g
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s - 1) h f (by omega)) (by omega)) =
      _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) g
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := (-s - 1) + 1) (_root_.SerrePositivity.DifferentialGraded.differential R h) f (by omega)) (by omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, differential_compose, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add,
    smul_smul, Int.units_mul_self, one_smul, _root_.SerrePositivity.DifferentialGraded.differential_compose, hf,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]

/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateBoundary_sub_unit {x y : D} (s : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y x s)
    (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0)
    (hgf : _root_.SerrePositivity.DifferentialGraded.compose R g f (neg_add_cancel s) = (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R y y (-1)) (u : _root_.SerrePositivity.DifferentialGraded.GradedHom R y y 0)
    (hu : (_root_.SerrePositivity.DifferentialGraded.homObject R D y y).d (-1) 0 h = u - (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val) :
    _root_.SerrePositivity.DifferentialGraded.differential R (s.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (n := (-1 : ℤ)) g
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s - 1) h f (by omega)) (by omega)) =
      _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) g (_root_.SerrePositivity.DifferentialGraded.compose R (n := (-s - 1) + 1) u f (by omega)) (by omega) -
        (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  change _root_.SerrePositivity.DifferentialGraded.differential R h = (u - (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val : _root_.SerrePositivity.DifferentialGraded.GradedHom R y y 0) at hu
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedConjugateBoundary R D s f g hf hg h, hu, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]
  refine congrArg₂ (· - ·) rfl ?_
  calc
    _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val (by omega)) f
        (neg_add_cancel s) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D f (unitElement R y).val g (by omega) (by omega) (by omega)
        (neg_add_cancel s)
    _ = _ := by rw [_root_.SerrePositivity.DifferentialGraded.compose_unit, hgf]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedConjugateComposite {x y z : D} (s : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y x s)
    (π : _root_.SerrePositivity.DifferentialGraded.GradedHom R z y 0) (σ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z 0) :
    _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) g
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := (-s - 1) + 1)
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) π σ (by omega)) f (by omega)) (by omega) =
      _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g π (by omega))
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ f (add_zero _)) (neg_add_cancel s) := by
  calc
    _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ))
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) π σ (by omega)) (by omega))
        f (neg_add_cancel s) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D f (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) π σ (by omega)) g
        (by omega) (by omega) (by omega)
        (neg_add_cancel s)
    _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ))
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g π (by omega)) σ (by omega))
        f (neg_add_cancel s) := by
      congr 1
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D σ π g (by omega) (by omega) (by omega) (by omega)
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D f σ (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g π (by omega))
      (add_zero _) (by omega) (neg_add_cancel s) (neg_add_cancel s)).symm
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgGradedTransferInverseComposite {x y z : D} (s : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y x s)
    (hfg : _root_.SerrePositivity.DifferentialGraded.compose R f g (add_neg_cancel s) = (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val)
    (π : _root_.SerrePositivity.DifferentialGraded.GradedHom R z y 0) (σ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z 0) :
    _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ f (add_zero _))
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) g π (by omega)) (add_neg_cancel s) =
        _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) σ π (by omega) := by
  calc
    _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ))
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ f (add_zero _)) g
          (add_neg_cancel s)) π (by omega) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D π g (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ f (add_zero _))
        (by omega) (add_neg_cancel s) (add_neg_cancel s) (by omega)
    _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ))
        (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) σ (_root_.SerrePositivity.DifferentialGraded.compose R f g (add_neg_cancel s)) (by omega))
        π (by omega) := by
      congr 1
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D g f σ (add_neg_cancel s) (add_zero _)
        (by omega) (add_neg_cancel s)).symm
    _ = _ := by rw [hfg, _root_.SerrePositivity.DifferentialGraded.compose_unit]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
