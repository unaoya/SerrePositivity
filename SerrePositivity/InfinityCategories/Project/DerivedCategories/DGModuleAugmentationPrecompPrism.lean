module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationPrecompData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationUnlifted
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (A C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ全 HA データから得る実 prism 単体は、入力前合成を厳密に保つ。 -/
lemma dgModuleAugmentationPrismSimplex_precomp {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) n)
    (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)) β =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R A E (H.comp F) s β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_precomp R A C E H F s.toSimplexData β
/-- 元の実円柱写像は、入力前合成と全単体上で厳密に可換。 -/
lemma dgModuleAugmentationNervePrism_precomp :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F) ▷ (Δ[1] : SSet)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNervePrism R C E F =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNervePrism R A E (H.comp F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact congrArg (fun t => t.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)))
    (dgModuleAugmentationPrismSimplex_precomp R A C E H F s.1
      (SSet.stdSimplex.objEquiv s.2).toOrderHom)
variable (A₀ C₀ : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A₀] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C₀]
  (E₀ : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E₀] [Small.{u} E₀]
  (H₀ : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A₀ C₀) (F₀ : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C₀ (_root_.SerrePositivity.DifferentialGraded.RightModule R E₀))
/-- 元の全加群 nerve 上の同じ実ホモトピーも、入力前合成を厳密に保つ。 -/
lemma dgModuleAugmentationUnliftedHomotopy_precomp :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A₀ C₀ E₀ H₀ F₀) ▷ (Δ[1] : SSet)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C₀ E₀ F₀).h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R A₀ E₀ (H₀.comp F₀)).h := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNervePrism R C₀ E₀ F₀ ≫ _) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNervePrism R A₀ E₀ (H₀.comp F₀) ≫ _
  rw [← Category.assoc, dgModuleAugmentationNervePrism_precomp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
