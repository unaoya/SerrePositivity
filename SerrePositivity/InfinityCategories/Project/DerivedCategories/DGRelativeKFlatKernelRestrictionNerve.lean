module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelComparisonHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
/-- 半自由入力上の通常 K-flat 作用の実包含後は、元の同じ通常 tensor の nerve である。 -/
lemma dgRelativeKFlatKernelNerve_semifree_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm
/-- 半自由入力上の同じ通常 K-flat 作用と分解は、元の通常 tensor の nerve と分解に等しい。 -/
lemma dgRelativeKFlatKernelNerve_semifree_resolution :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
/-- 同じ元の raw factor 比較を、K-flat の通常作用の同じ端点へ揃える。 -/
def dgRelativeKFlatKernelRestrictionNerveIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E) := by
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P) rfl ?_
  simpa only [Category.assoc] using congrArg
    (fun m => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution R D E P hP).symm
/-- K-flat の端点へ揃えても、元の半自由通常 tensor の raw factor の指定値を保持する。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_heq :
    HEq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) := by
  have h : HEq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P) := by
    unfold dgRelativeKFlatKernelRestrictionNerveIso
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso_heq R D E P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
