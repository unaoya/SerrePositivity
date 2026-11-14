module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Morita.Kernel
/-!
概要：任意の balanced tensor と双加群作用は、左加群側の次数別全射性を保つ。
方針：同じ斉次 tensor 生成元の持ち上げと各次数の線形射の外延性で全射を証明する。
規約：平坦性も元の出力の射影性も不要。使われ方：双加群準同型の実分解比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 任意の右加群との balanced tensor は、左加群射の同じ全次数全射性を保つ。 -/
lemma balancedTensor_map_leftModule_degree_surjective (M : ModuleCategory R D)
    {N N' : LeftModuleCategory R D} (g : N ⟶ N')
    (hg : ∀ (x : D) (j : ℤ), Function.Surjective (((leftModuleEvaluation R D x).map g).f j))
    (n : ℤ) : Function.Surjective ((BalancedTensor.map R D (𝟙 M) g).f n) := by
  apply (ModuleCat.epi_iff_surjective _).1
  apply (Preadditive.epi_iff_cancel_zero _).2
  intro V b hb
  apply BalancedTensor.degree_element_ext R D
    (ForgetEnrichment.to (Complex R) M) (ForgetEnrichment.to (Complex R) N') b 0
  intro x r s hn m v
  obtain ⟨t, ht⟩ := hg x s v
  have hm := BalancedTensor.map_element R D (𝟙 M) g x m t hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f] at hm
  rw [ht] at hm
  have h := ConcreteCategory.congr_hom hb
    (BalancedTensor.element R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N) x m t hn)
  change b ((BalancedTensor.map R D (𝟙 M) g).f n
    (BalancedTensor.element R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N) x m t hn)) = 0 at h
  rw [hm] at h
  exact h
variable (E : Type w) [DGCategory R E] [Small.{u} E]
/-- 双加群の両対象・全次数での全射性は、任意の実加群上の同じ tensor 射の全射性を与える。 -/
lemma dgKernelTensorMap_degree_surjective {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : ∀ (e : E) (d : D) (j : ℤ),
      Function.Surjective (((BimoduleCategory.valueEvaluation R E D e d).map f).f j))
    (M : ModuleCategory R D) :
    moduleDegreewiseSurjective R E ((Morita.kernelTensorMap R D E f).app M) := by
  intro e n
  change Function.Surjective (((moduleEvaluation R E e).map
    ((Morita.kernelTensorMap R D E f).app M)).f n)
  rw [Morita.kernelTensorMap_value]
  exact balancedTensor_map_leftModule_degree_surjective R D M
    ((BimoduleCategory.leftEvaluation R E D e).map f)
    (fun d j => by simpa only [BimoduleCategory.leftEvaluation_map_eval] using! hf e d j) n
end SerrePositivity.InfinityCategories.Project.DerivedCategories
