module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedExactness
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeSemiorthogonal
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackStable
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants KST.Spectra
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingCanonicalLaxPullback_isStable :
    IsStable (F2.laxPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) := by
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C)) :=
    (dgGluingStableInput.{u, v, w} R C hC).isStable
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (dgNerve R D)) :=
    (dgGluingStableInput.{u, w, v} R D hD).isStable
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)) :=
    (dgGluingStableModuleCategory.{u, v, w} R C).isStable
  let := dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC
  let := dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD
  exact F2.laxPullback_isStable _ _

lemma dgGluingCanonicalLaxPullback_cofiber_iff
    (t : ZeroTriangle (F2.laxPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M))) :
    IsPushoutSquare t.square ↔
      IsPushoutSquare (t.square ≫ F2.laxPullbackFst
        (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)) ∧
      IsPushoutSquare (t.square ≫ F2.laxPullbackSnd
        (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)) := by
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C)) :=
    (dgGluingStableInput.{u, v, w} R C hC).isStable
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (dgNerve R D)) :=
    (dgGluingStableInput.{u, w, v} R D hD).isStable
  let : IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)) :=
    (dgGluingStableModuleCategory.{u, v, w} R C).isStable
  let := dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC
  let := dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD
  exact F2.isPushoutSquare_laxPullback_iff_of_zero_corner _ _ t

def dgGluingCanonicalNativeSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition (dgGluingStableInput.{u, w, v} R D hD)
      (dgGluingStableInput.{u, v, w} R C hC) (dgGluingStableObject R C D M hC hD) :=
  dgGluingNativeSemiorthogonal R C D M hC hD
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD)
lemma dgGluingCanonicalNativeSemiorthogonal_projection :
    (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).projection =
      dgGluingStableLeftProjection R C D M hC hD :=
  dgGluingNativeSemiorthogonal_projection R C D M hC hD _ _
lemma dgGluingCanonicalNativeSemiorthogonal_retraction :
    (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).retraction =
      dgGluingStableRightProjection R C D M hC hD :=
  dgGluingNativeSemiorthogonal_retraction R C D M hC hD _ _
variable (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{max (u + 1) v w} ⟶ Sp.{max (u + 1) v w})
  (hΦ : IsLocalizingInvariant Φ)
def dgGluingCanonicalTammeProjectionEquivalence :
    SpectrumHo.obj (value Φ (dgGluingStableObject R C D M hC hD)) ≅
      SpectrumHo.obj (Binary.obj (value Φ (dgGluingStableInput.{u, v, w} R C hC))
        (value Φ (dgGluingStableInput.{u, w, v} R D hD))) :=
  dgGluingTammeProjectionEquivalence R C D M hC hD Φ
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) hΦ
lemma dgGluingCanonicalTammeProjectionEquivalence_fst :
    (dgGluingCanonicalTammeProjectionEquivalence R C D M hC hD Φ hΦ).hom ≫
      SpectrumHo.hom (Binary.fst _ _) =
        SpectrumHo.hom (valueMap Φ (dgGluingStableLeftProjection R C D M hC hD)) :=
  dgGluingTammeProjectionEquivalence_fst R C D M hC hD Φ _ _ hΦ
lemma dgGluingCanonicalTammeProjectionEquivalence_snd :
    (dgGluingCanonicalTammeProjectionEquivalence R C D M hC hD Φ hΦ).hom ≫
      SpectrumHo.hom (Binary.snd _ _) =
        SpectrumHo.hom (valueMap Φ (dgGluingStableRightProjection R C D M hC hD)) :=
  dgGluingTammeProjectionEquivalence_snd R C D M hC hD Φ _ _ hΦ

end SerrePositivity.InfinityCategories
