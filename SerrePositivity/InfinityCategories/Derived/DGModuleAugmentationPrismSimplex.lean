module

public import SerrePositivity.InfinityCategories.Derived.AugmentationProofCases
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationSamePhaseEquation
/-!
概要：元の実 augmentation 切断補正和が全 HA 方程式を満たす単体を構成する。
方針：混合・同相の実方程式を結合し、逆向きの相を単調性で除く。
規約：添字変更との自然性は別工程。使われ方：全 augmentation prism の単体写像。
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
  {n : ℕ} (s : Simplex R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実 augmentation 候補の、全端点相・全正しい添字における HA 方程式。 -/
lemma dgModuleAugmentationPrismData_equation
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential R ((dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (dgModuleAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
  rcases hp (β a) with ha0 | ha1
  · rcases hp (β b) with hb0 | hb1
    · exact dgModuleAugmentationPrismData_equation_same R C E F s β 0 I a b k
        hI ha hb hk ha0 hb0
    · exact dgModuleAugmentationPrismData_equation_mixed R C E F s β I a b k
        hI ha hb hk ha0 hb1
  · rcases hp (β b) with hb0 | hb1
    · have hab : a ≤ b := by
        rw [ha, hb]
        exact (I.isLeast_min' _).2 (I.max'_mem _)
      have hh := β.monotone hab
      rw [ha1, hb0] at hh
      change (1 : ℕ) ≤ 0 at hh
      omega
    · exact dgModuleAugmentationPrismData_equation_same R C E F s β 1 I a b k
        hI ha hb hk ha1 hb1
/-- 同じ実切断補正和と実対象から得られる、全 HA 方程式を持つ単体。 -/
def dgModuleAugmentationPrismSimplex (β : Fin (n + 1) →o Fin 2) :
    Simplex R (RightModule R E) n where
  toSimplexData := dgModuleAugmentationPrismData R C E F s.toSimplexData β
  equation I a b k hI ha hb hk :=
    dgModuleAugmentationPrismData_equation R C E F s β I a b k hI ha hb hk
/-- 実候補単体の相零端点は、同じ半自由出力射影の単体像。 -/
lemma dgModuleAugmentationPrismSimplex_zero :
    dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (0 : Fin 2)) =
      s.map (dgModuleAugmentationSource R C E F) := by
  apply Simplex.ext
  exact dgModuleAugmentationPrismData_zero R C E F s.toSimplexData
/-- 実候補単体の相一端点は、元の同じ入力像の単体像。 -/
lemma dgModuleAugmentationPrismSimplex_one :
    dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (1 : Fin 2)) =
      s.map (dgModuleAugmentationTarget R C E F) := by
  apply Simplex.ext
  exact dgModuleAugmentationPrismData_one R C E F s.toSimplexData
end SerrePositivity.InfinityCategories
