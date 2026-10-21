module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedSurjectiveComparisonAction
public import SerrePositivity.InfinityCategories.Derived.FunctorSplitSpanComparison
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedQuasiIsoMapAction
public import SerrePositivity.InfinityCategories.Derived.DGKernelQuasiIsoComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_comparison_hom
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E D f) :
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf).hom =
      (dgKernelDerivedFunctorHomFunctor R D E).map f := by
  let el := dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (dgBimoduleQuasiIsoSpanLeft_quasiIso R E D P Q)
    (dgBimoduleQuasiIsoSpanLeft_degree_surjective R E D P Q)
  let er := dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (dgBimoduleQuasiIsoSpanRight R E D f)
    (dgBimoduleQuasiIsoSpanRight_quasiIso R E D f hf)
    (dgBimoduleQuasiIsoSpanRight_degree_surjective R E D f)
  change el.inv ≫ er.hom = _
  exact functor_splitSpan_comparison_hom (dgKernelDerivedFunctorHomFunctor R D E)
    (dgBimoduleQuasiIsoSpanSection R E D P Q)
    (dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (dgBimoduleQuasiIsoSpanRight R E D f) f
    (dgBimoduleQuasiIsoSpanSection_left R E D P Q)
    (dgBimoduleQuasiIsoSpanSection_right R E D f) el er
    (dgKernelDerivedInfinity_surjective_comparison_hom R D E _ _ _)
    (dgKernelDerivedInfinity_surjective_comparison_hom R D E _ _ _)
lemma dgKernelDerivedInfinity_comparison_eq_mapIso
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E D f) :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf =
      dgKernelDerivedQuasiIsoMapIso R D E f hf := by
  apply Iso.ext
  exact dgKernelDerivedInfinity_comparison_hom R D E f hf
end SerrePositivity.InfinityCategories
