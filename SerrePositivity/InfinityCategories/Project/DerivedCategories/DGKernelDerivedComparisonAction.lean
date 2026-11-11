module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedSurjectiveComparisonAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorSplitSpanComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedQuasiIsoMapAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelQuasiIsoComparison
/-!
概要：元の一般準同型の span 比較と実導来射作用を同じ全関手射で照合する。
方針：実切断の二合成と同じ関手の恒等・合成則を使う。
規約：従来の指定比較を保つ。使われ方：模型変更の自然性と合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_comparison_hom
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f := by
  let el := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft_quasiIso R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft_degree_surjective R E D P Q)
  let er := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight R E D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight_quasiIso R E D f hf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight_degree_surjective R E D f)
  change el.inv ≫ er.hom = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functor_splitSpan_comparison_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanSection R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight R E D f) f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanSection_left R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanSection_right R E D f) el er
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_surjective_comparison_hom R D E _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_surjective_comparison_hom R D E _ _ _)
lemma dgKernelDerivedInfinity_comparison_eq_mapIso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedQuasiIsoMapIso R D E f hf := by
  apply Iso.ext
  exact dgKernelDerivedInfinity_comparison_hom R D E f hf
end SerrePositivity.InfinityCategories.Project.DerivedCategories
