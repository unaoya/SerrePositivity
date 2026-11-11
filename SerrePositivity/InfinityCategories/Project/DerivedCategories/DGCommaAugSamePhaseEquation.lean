module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugSamePhaseCoefficients
/-!
概要：両端が同相の実候補について、任意の正しい添字の HA 方程式を証明する。
方針：相の単調性から全内部点も同相とし、元の実 dg 関手の単体方程式へ移す。
規約：部分集合の外の相は任意。使われ方：全 augmentation 候補単体の完成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 同相の実線形境界は、元の相関手による同じ線形境界の像。 -/
lemma dgCommaAugmentationSameTransport_linearBoundary
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hpa : β a = p) (hpb : β b = p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s β p a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).linearBoundary I a b k) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f (k + 1)
        (s.linearBoundary I a b k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary, Units.smul_def, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport_homOrZero]
/-- 同相の実切断合成は、元の相関手による同じ切断合成の像。 -/
lemma dgCommaAugmentationSameTransport_cut
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hpa : β a = p) (hpj : β j = p) (hpb : β b = p)
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s β p a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s β p a hpa
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s β p j hpj
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s β p b hpb
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport_homOrZero R C E F s β p
    (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hpj hpb
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport_homOrZero R C E F s β p
    (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hpa hpj
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport hy hz rfl _ = _ at hr
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport hx hy rfl _ = _ at hl
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose, dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose hx hy hz rfl rfl rfl, hr, hl,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p)]
/-- 同相の実二次境界は、元の相関手による同じ二次境界の像。 -/
lemma dgCommaAugmentationSameTransport_quadraticBoundary
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = p) (hpb : β b = p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s β p a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).quadraticBoundary I a b k) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f (k + 1)
        (s.quadraticBoundary I a b k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary, Units.smul_def, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have haj : a ≤ j := by rw [ha]; exact (I.isLeast_min' _).2 hm.1
  have hjb : j ≤ b := by rw [hb]; exact (I.isGreatest_max' _).2 hm.1
  have hl : p ≤ β j := by simpa only [hpa] using β.monotone haj
  have hr : β j ≤ p := by simpa only [hpb] using β.monotone hjb
  have hpj : β j = p := le_antisymm hr hl
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hm.1
    omega
  rw [dgCommaAugmentationSameTransport_cut R C E F s β p I a b k j hpa hpj hpb hsum]
/-- 同じ実候補は、任意の同相端点と正しい添字で元の HA 方程式を満たす。 -/
lemma dgCommaAugmentationPrismData_equation_same
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = p) (hpb : β b = p) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s.toSimplexData β p a b
    (k + 1) hpa hpb).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic, map_sub,
    dgCommaAugmentationSameTransport_linearBoundary,
    dgCommaAugmentationSameTransport_quadraticBoundary R C E F s.toSimplexData β p
      I a b k hI ha hb hk hpa hpb]
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s.toSimplexData β p a hpa
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s.toSimplexData β p b hpb
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential hx hz (rfl : k = k)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s.toSimplexData β p a b
    (k + 1) hpa hpb
    (differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
      I a b k hI ha hb hk)) =
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s.toSimplexData β p a b k
      hpa hpb ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk)) at hd
  rw [hd]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hx hz (rfl : k = k)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f k
      (s.hom I a b k hI ha hb hk))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_phase R C E F s.toSimplexData β p I a b k
      hI ha hb hk hpa hpb)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSameTransport R C E F s.toSimplexData β p a b k hpa hpb
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk) = _ at he
  rw [he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p), s.equation,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic, map_sub]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
