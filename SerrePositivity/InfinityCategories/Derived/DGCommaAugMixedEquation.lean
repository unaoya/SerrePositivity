module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugMixedQuadraticBoundary
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 同じ実候補は、任意の混合端点と正しい全添字で HA 方程式を満たす。 -/
lemma dgCommaAugmentationPrismData_equation_mixed
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    differential R ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (dgCommaAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  apply (dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb).injective
  rw [SimplexData.rhs_eq_linear_sub_quadratic, map_sub,
    dgCommaAugmentationMixedTransport_linearBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb,
    dgCommaAugmentationMixedTransport_quadraticBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb]
  have hx := dgCommaAugmentationPrismData_obj_zero R C E F s.toSimplexData β a hpa
  have hz := dgCommaAugmentationPrismData_obj_one R C E F s.toSimplexData β b hpb
  have hd := gradedHomTransport_differential hx hz (rfl : k = k)
    ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
  change dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb
    (differential R ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
      I a b k hI ha hb hk)) =
    differential R (dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b
      k hpa hpb ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk)) at hd
  rw [hd]
  have he := gradedHomTransport_eq_of_heq hx hz (rfl : k = k)
    ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
    (dgCommaAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk)
    (dgCommaAugmentationPrismData_hom_mixed R C E F s.toSimplexData β I a b k
      hI ha hb hk hpa hpb)
  change dgCommaAugmentationMixedTransport R C E F s.toSimplexData β a b k hpa hpb
    ((dgCommaAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk) = _ at he
  rw [he]
  change (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
    (dgCommaAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) = _
  rw [dgCommaAugmentationPrismMixedHom_differential_corrections R C E F s β I a b k
    hI ha hb hk, dgCommaAugmentationBase_simplex_differential]
  simp only [map_sub]
  abel
end SerrePositivity.InfinityCategories
