module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorCompositionSemifreeTransport
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.F2.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransportAlgebra
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 同じ K-flat 合成比較の半自由入力制限は、実包含後に元の通常 tensor 比較を回収する。 -/
lemma dgRelativeKFlatKernelCompositionIso_semifree_inclusion_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatModuleInclusion R K))
      (dgKernelTensorCompositionSemifreeIso R D E K P Q) := by
  let a := dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ
  let N₀ := dgRelativeKFlatKernelNerve R D E P hP
  let N₁ := dgRelativeKFlatKernelNerve R E K Q hQ
  let i := dgRelativeKFlatModuleInclusion R D
  let j := dgSemifreeToRelativeKFlatNerve R D
  let k := dgRelativeKFlatModuleInclusion R K
  let c := dgKernelTensorCompositionNerveIso R D E K P Q
  have hs : (N₀ ≫ N₁) ≫ k =
      i ≫ dgNerve.map (Morita.kernelTensor R D E P) ≫
        dgNerve.map (Morita.kernelTensor R E K Q) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion,
      ← Category.assoc N₀, dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have ht := dgRelativeKFlatKernelNerve_inclusion R D K (BimoduleTensor.compose R K E D Q P)
    (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)
  have h1 := F2.functorIso_precomp_heq_of_heq (c.precomp i) (a.postcomp k)
    hs.symm ht.symm (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E K P Q hP hQ) j
  have h2 := heq_of_eq (F2.functorIso_precomp_postcomp a j k)
  have h3 := heq_of_eq (F2.functorIso_precomp_precomp c i j)
  have h4 := F2.functorIso_precomp_heq_of_map_eq c (dgSemifreeToRelativeKFlatNerve_inclusion R D)
  exact h2.trans (h1.trans (h3.trans (h4.trans
    (dgKernelTensorCompositionSemifreeIso_heq R D E K P Q).symm)))

/-- 同じ半自由入力制限と分解後の比較は、元の通常 tensor 比較と同じ raw 分解への像。 -/
lemma dgRelativeKFlatKernelCompositionIso_semifree_resolution_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K))
      ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))) := by
  let a := (dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
    (dgSemifreeToRelativeKFlatNerve R D)
  let N₀ := dgRelativeKFlatKernelNerve R D E P hP
  let N₁ := dgRelativeKFlatKernelNerve R E K Q hQ
  let i := dgRelativeKFlatModuleInclusion R D
  let j := dgSemifreeToRelativeKFlatNerve R D
  let k := dgRelativeKFlatModuleInclusion R K
  let T := dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  have hs : (N₀ ≫ N₁) ≫ k =
      i ≫ dgNerve.map (Morita.kernelTensor R D E P) ≫
        dgNerve.map (Morita.kernelTensor R E K Q) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion,
      ← Category.assoc N₀, dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have hss : (j ≫ (N₀ ≫ N₁)) ≫ k =
      dgNerve.map ((dgSemifreeKernelModuleDG R D E P).comp (Morita.kernelTensor R E K Q)) := by
    calc
      _ = j ≫ ((N₀ ≫ N₁) ≫ k) := Category.assoc _ _ _
      _ = j ≫ i ≫ dgNerve.map (Morita.kernelTensor R D E P) ≫
          dgNerve.map (Morita.kernelTensor R E K Q) := congrArg (fun m => j ≫ m) hs
      _ = dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)) ≫ dgNerve.map (Morita.kernelTensor R D E P) ≫
            dgNerve.map (Morita.kernelTensor R E K Q) := by
        rw [← Category.assoc j i, dgSemifreeToRelativeKFlatNerve_inclusion]
      _ = _ := by simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp, Category.assoc]
  have hts := dgRelativeKFlatKernelNerve_semifree_inclusion R D K
    (BimoduleTensor.compose R K E D Q P)
    (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)
  have h1 : HEq (a.postcomp (dgRelativeKFlatResolution R K)) ((a.postcomp k).postcomp T) :=
    heq_of_eq (F2.functorIso_postcomp_postcomp a k T).symm
  have h2 := F2.functorIso_postcomp_heq_of_heq
    (dgKernelTensorCompositionSemifreeIso R D E K P Q) (a.postcomp k) hss.symm hts.symm
    (dgRelativeKFlatKernelCompositionIso_semifree_inclusion_heq R D E K P Q hP hQ) T
  exact h1.trans h2
end SerrePositivity.InfinityCategories
