module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelComparisonHom
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport
/-!
概要：元の半自由制限比較を、通常 K-flat 作用と同じ出力分解の端点へ揃える。
方針：通常作用の実包含式と元の出力分解を保って端点だけを輸送する。
規約：新しい比較を選ばない。使われ方：K-flat 圏内の augmentation 正方形と合成子比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- 半自由入力上の通常 K-flat 作用の実包含後は、元の同じ通常 tensor の nerve である。 -/
lemma dgRelativeKFlatKernelNerve_semifree_inclusion :
    (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP) ≫
      dgRelativeKFlatModuleInclusion R E = dgNerve.map (dgSemifreeKernelModuleDG R D E P) := by
  rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    dgSemifreeToRelativeKFlatNerve_inclusion]
  exact (dgNerve.map_comp _ _).symm
/-- 半自由入力上の同じ通常 K-flat 作用と分解は、元の通常 tensor の nerve と分解に等しい。 -/
lemma dgRelativeKFlatKernelNerve_semifree_resolution :
    dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP ≫
      dgRelativeKFlatResolution R E =
    dgNerve.map (dgSemifreeKernelModuleDG R D E P) ≫
      dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)) := by
  rw [dgRelativeKFlatKernelNerve_resolution]
  simp only [dgRelativeKFlatKernelToDerived, ← Category.assoc,
    dgSemifreeToRelativeKFlatNerve_inclusion, dgSemifreeKernelModuleDG, dgNerve.map_comp]
/-- 同じ元の raw factor 比較を、K-flat の通常作用の同じ端点へ揃える。 -/
def dgRelativeKFlatKernelRestrictionNerveIso :
    FunctorIso (dgKernelDerivedInfinity R D E P)
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP ≫
        dgRelativeKFlatResolution R E) := by
  refine F2.functorIsoOfEq (dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P) rfl ?_
  simpa only [Category.assoc] using congrArg
    (fun m => dgSemifreeToRelativeKFlatNerve R D ≫ m)
    (dgRelativeKFlatKernelNerve_resolution R D E P hP).symm
/-- K-flat の端点へ揃えても、元の半自由通常 tensor の raw factor の指定値を保持する。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_heq :
    HEq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) := by
  have h : HEq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
      (dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P) := by
    unfold dgRelativeKFlatKernelRestrictionNerveIso
    exact F2.functorIsoOfEq_heq _ _ _
  exact h.trans (dgKernelDerivedInfinity_relativeKFlatRestrictionIso_heq R D E P)
end SerrePositivity.InfinityCategories
