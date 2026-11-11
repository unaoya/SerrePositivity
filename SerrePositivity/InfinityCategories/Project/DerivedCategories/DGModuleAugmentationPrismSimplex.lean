module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.AugmentationProofCases
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationSamePhaseEquation
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実 augmentation 候補の、全端点相・全正しい添字における HA 方程式。 -/
lemma dgModuleAugmentationPrismData_equation
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s.toSimplexData β).hom
        I a b k hI ha hb hk) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s.toSimplexData β).rhs I a b k hI ha hb hk := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.augmentation_proof_of_endpoint_phases β I a b hI ha hb
    (fun p haP hbP ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_equation_same R C E F s β p I a b k
      hI ha hb hk haP hbP)
    (fun ha0 hb1 ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_equation_mixed R C E F s β I a b k
      hI ha hb hk ha0 hb1)
/-- 同じ実切断補正和と実対象から得られる、全 HA 方程式を持つ単体。 -/
def dgModuleAugmentationPrismSimplex (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R E) n where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s.toSimplexData β
  equation I a b k hI ha hb hk :=
    dgModuleAugmentationPrismData_equation R C E F s β I a b k hI ha hb hk
/-- 実候補単体の相零端点は、同じ半自由出力射影の単体像。 -/
lemma dgModuleAugmentationPrismSimplex_zero :
    dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (0 : Fin 2)) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_zero R C E F s.toSimplexData
/-- 実候補単体の相一端点は、元の同じ入力像の単体像。 -/
lemma dgModuleAugmentationPrismSimplex_one :
    dgModuleAugmentationPrismSimplex R C E F s (OrderHom.const _ (1 : Fin 2)) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_one R C E F s.toSimplexData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
