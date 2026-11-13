module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGKernelTensorCompositionSemifreeTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
/-!
概要：元の K-flat 通常合成比較を半自由入力と同じ出力分解上で回収する。
方針：元の通常 tensor 比較の指定値と実包含・出力分解の厳密式を保つ。
規約：元の比較の定義を変更しない。使われ方：元の導来合成子の K-flat 共通経路計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E)
/-- 同じ K-flat 合成比較の半自由入力制限は、実包含後に元の通常 tensor 比較を回収する。 -/
lemma dgRelativeKFlatKernelCompositionIso_semifree_inclusion_heq
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R K))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso R D E K P Q) := by
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ
  let N₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP
  let N₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E K Q hQ
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D
  let k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R K
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E K P Q
  have hs : (N₀ ≫ N₁) ≫ k =
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K Q) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion,
      ← Category.assoc N₀, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D K (BimoduleTensor.compose R K E D Q P)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)
  have h1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (c.precomp i) (a.postcomp k)
    hs.symm ht.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E K P Q hP hQ) j
  have h2 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp a j k)
  have h3 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp c i j)
  have h4 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion R D)
  exact h2.trans (h1.trans (h3.trans (h4.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso_heq R D E K P Q).symm)))

/-- 同じ半自由入力制限と分解後の比較は、元の通常 tensor 比較と同じ raw 分解への像。 -/
lemma dgRelativeKFlatKernelCompositionIso_semifree_resolution_heq
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R K))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)
  let N₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP
  let N₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E K Q hQ
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D
  let k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R K
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  have hs : (N₀ ≫ N₁) ≫ k =
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K Q) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion,
      ← Category.assoc N₀, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have hss : (j ≫ (N₀ ≫ N₁)) ≫ k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P).comp (Morita.kernelTensor R E K Q)) := by
    calc
      _ = j ≫ ((N₀ ≫ N₁) ≫ k) := Category.assoc _ _ _
      _ = j ≫ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K Q) := congrArg (fun m => j ≫ m) hs
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K Q) := by
        rw [← Category.assoc j i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
      _ = _ := by simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
  have hts := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_semifree_inclusion R D K
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R K E D Q P)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)
  have h1 : HEq (a.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R K)) ((a.postcomp k).postcomp T) :=
    heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp a k T).symm
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso R D E K P Q) (a.postcomp k) hss.symm hts.symm
    (dgRelativeKFlatKernelCompositionIso_semifree_inclusion_heq R D E K P Q hP hQ) T
  exact h1.trans h2
end SerrePositivity.InfinityCategories.Project.DerivedCategories
