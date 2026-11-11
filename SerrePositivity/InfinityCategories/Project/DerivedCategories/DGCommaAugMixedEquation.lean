module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugMixedQuadraticBoundary
/-!
概要：実混合候補の全 HA 方程式を元の同じ実係数で証明する。
方針：相別係数の回収と Hom の線形移送、既証明の実微分式を使う。
規約：単体作用の自然性は別工程。使われ方：全 augmentation prism の単体構成。
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
/-- 同じ実候補は、任意の混合端点と正しい全添字で HA 方程式を満たす。 -/
lemma dgCommaAugmentationPrismData_equation_mixed
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic, map_sub,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport_linearBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport_quadraticBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb]
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_zero R C E F s.toSimplexData β a hpa
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R C E F s.toSimplexData β b hpb
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential hx hz (rfl : k = k)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb
    (differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
      I a b k hI ha hb hk)) =
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
      k hpa hpb ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk)) at hd
  rw [hd]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hx hz (rfl : k = k)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R C E F s.toSimplexData β I a b k
      hI ha hb hk hpa hpb)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b k hpa hpb
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk) = _ at he
  rw [he]
  change (_root_.SerrePositivity.DifferentialGraded.homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_differential_corrections R C E F s β I a b k
    hI ha hb hk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBase_simplex_differential]
  simp only [map_sub]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
