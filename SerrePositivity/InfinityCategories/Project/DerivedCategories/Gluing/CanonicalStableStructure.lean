module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedExactness
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeSemiorthogonal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackStable
/-!
概要：正本 gluing の安定 lax pullback と native 半直交分解へ、実二脚の完全性を供給する。
方針：D-14 の完全性で隔離入力を実例化し、F2 と K-8b の同じ射影を持つ構成を適用する。
規約：元 C・D の前三角性だけを入力とし、完全性を追加仮定にしない。
使われ方：Tamme Lemma 8 と native gluing の分裂の無条件の公開入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants KST.Spectra
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingCanonicalLaxPullback_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC).isStable
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD).isStable
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableModuleCategory.{u, v, w} R C).isStable
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_isStable _ _

lemma dgGluingCanonicalLaxPullback_cofiber_iff
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC).isStable
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD).isStable
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableModuleCategory.{u, v, w} R C).isStable
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isPushoutSquare_laxPullback_iff_of_zero_corner _ _ t

def dgGluingCanonicalNativeSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeSemiorthogonal R C D M hC hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD)
lemma dgGluingCanonicalNativeSemiorthogonal_projection :
    (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).projection =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLeftProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeSemiorthogonal_projection R C D M hC hD _ _
lemma dgGluingCanonicalNativeSemiorthogonal_retraction :
    (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).retraction =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableRightProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeSemiorthogonal_retraction R C D M hC hD _ _
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v w} ⟶ Sp.{max (u + 1) v w})
  (hΦ : IsLocalizingInvariant Φ)
def dgGluingCanonicalTammeProjectionEquivalence :
    SpectrumHo.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)) ≅
      SpectrumHo.obj (Binary.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC))
        (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTammeProjectionEquivalence R C D M hC hD Φ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) hΦ
lemma dgGluingCanonicalTammeProjectionEquivalence_fst :
    (dgGluingCanonicalTammeProjectionEquivalence R C D M hC hD Φ hΦ).hom ≫
      SpectrumHo.hom (Binary.fst _ _) =
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLeftProjection R C D M hC hD)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTammeProjectionEquivalence_fst R C D M hC hD Φ _ _ hΦ
lemma dgGluingCanonicalTammeProjectionEquivalence_snd :
    (dgGluingCanonicalTammeProjectionEquivalence R C D M hC hD Φ hΦ).hom ≫
      SpectrumHo.hom (Binary.snd _ _) =
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableRightProjection R C D M hC hD)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTammeProjectionEquivalence_snd R C D M hC hD Φ _ _ hΦ

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
