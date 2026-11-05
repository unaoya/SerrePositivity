module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableLaxStructure
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableTammeComparison
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
/-!
概要：K-8b の実半直交分解を、元 dg gluing の共通宇宙の nerve へ戻す。
方針：元の比較同値と実随伴を合成し、元射影を両射影の厳密な比較式で回収する。
規約：二脚の完全性は上流供給待ちの明示入力。因子の順序は ⟨D,C⟩ を保つ。
使われ方：native gluing の分解と Tamme の分裂との整合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (hY : IsExactFunctor (dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingNativeDInclusion : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableInput.{u, w, v} R D hD)
    (dgGluingStableObject R C D M hC hD) :=
  ⟨(dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom ≫
    (dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeCInclusion : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableInput.{u, v, w} R C hC)
    (dgGluingStableObject R C D M hC hD) :=
  ⟨(dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom ≫
    (dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeRightAdjunction :
    QCatAdjunction (dgGluingUniverseLeftNerve R C D M)
      (dgGluingNativeCInclusion R C D M hC hD hY hM).hom := by
  have a := (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).toAdjunction.comp
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightAdjunction
  change QCatAdjunction (dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) _ at a
  rwa [dgGluingUniverseDerivedNerveLaxComparison_fst] at a
def dgGluingNativeLeftAdjunction :
    QCatAdjunction (dgGluingNativeDInclusion R C D M hC hD hY hM).hom
      (dgGluingUniverseRightNerve R C D M) := by
  have a := (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).leftAdjunction.comp
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.toAdjunction
  change QCatAdjunction _ (dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) at a
  rwa [dgGluingUniverseDerivedNerveLaxComparison_snd] at a
lemma dgGluingNativeDInclusion_isFullyFaithful :
    IsFullyFaithful (dgGluingNativeDInclusion R C D M hC hD hY hM).hom :=
  (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion_fullyFaithful.comp
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence.isFullyFaithful
lemma dgGluingNativeCInclusion_isFullyFaithful :
    IsFullyFaithful (dgGluingNativeCInclusion R C D M hC hD hY hM).hom :=
  (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion_fullyFaithful.comp
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence.isFullyFaithful

def dgGluingNativeDInclusion_left_iso :
    FunctorIso
      ((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
        dgGluingUniverseLeftNerve R C D M)
      ((dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom ≫
        F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (dgGluingUniverseDerivedCoefficient R C D M)) := by
  have hi := ((dgGluingUniverseDerivedNerveLaxEquivalence R C D M).invHomIso.precomp
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom).postcomp
      (F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
  simpa only [Category.assoc, dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    dgGluingUniverseDerivedNerveLaxComparison_fst, Category.id_comp, Category.comp_id,
    dgGluingNativeDInclusion, dgGluingStableComparisonInverse, Category.assoc] using! hi

lemma dgGluingNativeDInclusion_killed (d : (dgGluingStableInput.{u, w, v} R D hD).obj _⦋0⦌) :
    IsZeroVertex (((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
      dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌) d) :=
  ((dgGluingLaxSemiorthogonal R C D M hC hD hY hM).kills_inclusion d).of_vertexIso
    ((dgGluingNativeDInclusion_left_iso R C D M hC hD hY hM).app d).symm

lemma dgGluingNativeDInclusion_generates_kernel
    (x : (dgGluingStableObject R C D M hC hD).obj _⦋0⦌)
    (hx : IsZeroVertex ((dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌) x)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingNativeDInclusion R C D M hC hD hY hM) := by
  have hz : IsZeroVertex ((F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌) x)) := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M) (Opposite.op ⦋0⦌)) x
    exact he.symm ▸ hx
  obtain ⟨d, ⟨hd⟩⟩ := (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).generates_kernel _ hz
  refine ⟨d, ⟨?_⟩⟩
  exact (VertexIso.map hd (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv) ≪≫
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).homInvIso.app x

def dgGluingNativeSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition (dgGluingStableInput.{u, w, v} R D hD)
      (dgGluingStableInput.{u, v, w} R C hC) (dgGluingStableObject R C D M hC hD) := by
  let s := dgGluingLaxSemiorthogonal R C D M hC hD hY hM
  let e := dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  let : IsExactFunctor e.hom :=
    dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor R C D M
  refine {
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.inclusion := dgGluingNativeDInclusion R C D M hC hD hY hM
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.rightInclusion := dgGluingNativeCInclusion R C D M hC hD hY hM
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.retraction := ⟨e.hom ≫ s.retraction.hom, inferInstance⟩
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.projection := ⟨e.hom ≫ s.projection.hom, inferInstance⟩
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.leftAdjunction := s.leftAdjunction.comp e.symm.toAdjunction
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.rightAdjunction := e.toAdjunction.comp s.rightAdjunction
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.inclusion_fullyFaithful := dgGluingNativeDInclusion_isFullyFaithful R C D M hC hD hY hM
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.rightInclusion_fullyFaithful := dgGluingNativeCInclusion_isFullyFaithful R C D M hC hD hY hM
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.counit_isIso := ?_
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.kills_inclusion := ?_
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition.generates_kernel := ?_ }
  · have : IsIso e.toAdjunction.counit := by
      change IsIso e.adjointEquivalence.counit.hom
      infer_instance
    change IsIso (Bicategory.Adjunction.compCounit e.toAdjunction s.rightAdjunction)
    let : IsIso s.rightAdjunction.counit := s.counit_isIso
    dsimp only [Bicategory.Adjunction.compCounit, bicategoricalComp]
    infer_instance
  · intro d
    change IsZeroVertex (((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
      dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
        F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌) d)
    rw [dgGluingUniverseDerivedNerveLaxComparison_fst]
    exact dgGluingNativeDInclusion_killed R C D M hC hD hY hM d
  · intro x hx
    change IsZeroVertex ((dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
      F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌) x) at hx
    rw [dgGluingUniverseDerivedNerveLaxComparison_fst] at hx
    exact dgGluingNativeDInclusion_generates_kernel R C D M hC hD hY hM x hx

lemma dgGluingNativeSemiorthogonal_projection :
    (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).projection =
      dgGluingStableLeftProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M)
lemma dgGluingNativeSemiorthogonal_retraction :
    (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).retraction =
      dgGluingStableRightProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M)

lemma dgGluingNativeSemiorthogonal_isVerdier :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence (dgGluingNativeDInclusion R C D M hC hD hY hM)
      (dgGluingStableLeftProjection R C D M hC hD) := by
  have h := (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).isVerdier
  rw [dgGluingNativeSemiorthogonal_projection] at h
  exact h

lemma dgGluingDFactor_iff_nativeSemiorthogonal_image (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R C X.left ↔
      ULift.up (Simplex.vertex X) ∈
        _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingNativeDInclusion R C D M hC hD hY hM) := by
  rw [dgGluingDFactor_iff_stableLeftKernel]
  have h := (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).kernel
    (ULift.up (Simplex.vertex X))
  rw [dgGluingNativeSemiorthogonal_projection] at h
  exact h

lemma dgGluingNativeSemiorthogonal_mappingSpace
    (d : (dgGluingStableInput.{u, w, v} R D hD).obj _⦋0⦌)
    (c : (dgGluingStableInput.{u, v, w} R C hC).obj _⦋0⦌) :
    IsContractibleKan (pinchedHom
      ((dgGluingNativeDInclusion R C D M hC hD hY hM).hom.app (Opposite.op ⦋0⦌) d)
      ((dgGluingNativeCInclusion R C D M hC hD hY hM).hom.app (Opposite.op ⦋0⦌) c)) :=
  (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).semiorthogonal d c

end SerrePositivity.InfinityCategories
