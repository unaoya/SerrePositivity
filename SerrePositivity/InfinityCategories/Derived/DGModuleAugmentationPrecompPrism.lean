module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrecompData
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationUnlifted
/-!
概要：同じ実 augmentation の全 prism 単体と円柱写像は入力前合成を保つ。
方針：全 simplex data の一致を実単体へ移し、同じ対象宇宙の持ち上げ・下降を続ける。
規約：全時刻・全面・退化を含む写像を比較する。使われ方：指定分解比較と augmentation の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ全 HA データから得る実 prism 単体は、入力前合成を厳密に保つ。 -/
lemma dgModuleAugmentationPrismSimplex_precomp {n : ℕ}
    (s : Simplex R (DGModuleFunctorResolutionObject R A E (H.comp F)) n)
    (β : Fin (n + 1) →o Fin 2) :
    dgModuleAugmentationPrismSimplex R C E F
      (s.map (dgModuleResolutionPrecompFunctor R A C E H F)) β =
    dgModuleAugmentationPrismSimplex R A E (H.comp F) s β := by
  apply Simplex.ext
  exact dgModuleAugmentationPrismData_precomp R A C E H F s.toSimplexData β
/-- 元の実円柱写像は、入力前合成と全単体上で厳密に可換。 -/
lemma dgModuleAugmentationNervePrism_precomp :
    (dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F) ▷ (Δ[1] : SSet)) ≫
      dgModuleAugmentationNervePrism R C E F =
    dgModuleAugmentationNervePrism R A E (H.comp F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact congrArg (fun t => t.map (dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)))
    (dgModuleAugmentationPrismSimplex_precomp R A C E H F s.1
      (SSet.stdSimplex.objEquiv s.2).toOrderHom)
variable (A₀ C₀ : Type (max (u + 1) v)) [DGCategory R A₀] [DGCategory R C₀]
  (E₀ : Type v) [DGCategory R E₀] [Small.{u} E₀]
  (H₀ : DGFunctor R A₀ C₀) (F₀ : DGFunctor R C₀ (RightModule R E₀))
/-- 元の全加群 nerve 上の同じ実ホモトピーも、入力前合成を厳密に保つ。 -/
lemma dgModuleAugmentationUnliftedHomotopy_precomp :
    (dgNerve.map (dgModuleResolutionPrecompFunctor R A₀ C₀ E₀ H₀ F₀) ▷ (Δ[1] : SSet)) ≫
      (dgModuleAugmentationUnliftedHomotopy R C₀ E₀ F₀).h =
    (dgModuleAugmentationUnliftedHomotopy R A₀ E₀ (H₀.comp F₀)).h := by
  change _ ≫ (dgModuleAugmentationNervePrism R C₀ E₀ F₀ ≫ _) =
    dgModuleAugmentationNervePrism R A₀ E₀ (H₀.comp F₀) ≫ _
  rw [← Category.assoc, dgModuleAugmentationNervePrism_precomp]
end SerrePositivity.InfinityCategories
