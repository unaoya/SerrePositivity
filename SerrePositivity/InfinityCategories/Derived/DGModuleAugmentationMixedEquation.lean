module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationMixedQuadraticBoundary
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
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実候補は、任意の混合端点と正しい全添字で HA 方程式を満たす。 -/
lemma dgModuleAugmentationPrismData_equation_mixed
    (s : Simplex R (DGModuleFunctorResolutionObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    differential R ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (dgModuleAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  apply (dgModuleAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb).injective
  rw [SimplexData.rhs_eq_linear_sub_quadratic, map_sub,
    dgModuleAugmentationMixedTransport_linearBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb,
    dgModuleAugmentationMixedTransport_quadraticBoundary R C E F s.toSimplexData
      β I a b k hI ha hb hk hpa hpb]
  have hx := dgModuleAugmentationPrismData_obj_zero R C E F s.toSimplexData β a hpa
  have hz := dgModuleAugmentationPrismData_obj_one R C E F s.toSimplexData β b hpb
  have hd := gradedHomTransport_differential hx hz (rfl : k = k)
    ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
  change dgModuleAugmentationMixedTransport R C E F s.toSimplexData β a b
    (k + 1) hpa hpb
    (differential R ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom
      I a b k hI ha hb hk)) =
    differential R (dgModuleAugmentationMixedTransport R C E F s.toSimplexData β a b
      k hpa hpb ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk)) at hd
  rw [hd]
  have he := gradedHomTransport_eq_of_heq hx hz (rfl : k = k)
    ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk)
    (dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk)
    (dgModuleAugmentationPrismData_hom_mixed R C E F s.toSimplexData β I a b k
      hI ha hb hk hpa hpb)
  change dgModuleAugmentationMixedTransport R C E F s.toSimplexData β a b k hpa hpb
    ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom I a b k hI ha hb hk) = _ at he
  rw [he]
  change (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
    (dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) = _
  rw [dgModuleAugmentationPrismMixedHom_differential_corrections R C E F s β I a b k
    hI ha hb hk, dgModuleAugmentationBase_simplex_differential]
  simp only [map_sub]
  abel
end SerrePositivity.InfinityCategories
