module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.StableLaxStructure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.StableTammeComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
  (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingNativeDInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeCInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeRightAdjunction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M)
      (dgGluingNativeCInclusion R C D M hC hD hY hM).hom := by
  have a := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).toAdjunction.comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightAdjunction
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) _ at a
  rwa [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst] at a
def dgGluingNativeLeftAdjunction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (dgGluingNativeDInclusion R C D M hC hD hY hM).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M) := by
  have a := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).leftAdjunction.comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.toAdjunction
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) at a
  rwa [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd] at a
lemma dgGluingNativeDInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgGluingNativeDInclusion R C D M hC hD hY hM).hom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion_fullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence.isFullyFaithful
lemma dgGluingNativeCInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgGluingNativeCInclusion R C D M hC hD hY hM).hom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion_fullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence.isFullyFaithful

def dgGluingNativeDInclusion_left_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  have hi := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst, Category.id_comp, Category.comp_id,
    dgGluingNativeDInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparisonInverse, Category.assoc] using! hi

lemma dgGluingNativeDInclusion_killed (d : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌) d) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).kills_inclusion d).of_vertexIso
    ((dgGluingNativeDInclusion_left_iso R C D M hC hD hY hM).app d).symm

lemma dgGluingNativeDInclusion_generates_kernel
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD).obj _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌) x)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgGluingNativeDInclusion R C D M hC hD hY hM) := by
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌) x)) := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst R C D M) (Opposite.op ⦋0⦌)) x
    exact he.symm ▸ hx
  obtain ⟨d, ⟨hd⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).generates_kernel _ hz
  refine ⟨d, ⟨?_⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).homInvIso.app x

def dgGluingNativeSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor R C D M
  refine {
    inclusion := dgGluingNativeDInclusion R C D M hC hD hY hM
    rightInclusion := dgGluingNativeCInclusion R C D M hC hD hY hM
    retraction := ⟨e.hom ≫ s.retraction.hom, inferInstance⟩
    projection := ⟨e.hom ≫ s.projection.hom, inferInstance⟩
    leftAdjunction := s.leftAdjunction.comp e.symm.toAdjunction
    rightAdjunction := e.toAdjunction.comp s.rightAdjunction
    inclusion_fullyFaithful := dgGluingNativeDInclusion_isFullyFaithful R C D M hC hD hY hM
    rightInclusion_fullyFaithful := dgGluingNativeCInclusion_isFullyFaithful R C D M hC hD hY hM
    counit_isIso := ?_
    kills_inclusion := ?_
    generates_kernel := ?_ }
  · have : IsIso e.toAdjunction.counit := by
      change IsIso e.adjointEquivalence.counit.hom
      infer_instance
    change IsIso (Bicategory.Adjunction.compCounit e.toAdjunction s.rightAdjunction)
    let : IsIso s.rightAdjunction.counit := s.counit_isIso
    dsimp only [Bicategory.Adjunction.compCounit, bicategoricalComp]
    infer_instance
  · intro d
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((dgGluingNativeDInclusion R C D M hC hD hY hM).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌) d)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst]
    exact dgGluingNativeDInclusion_killed R C D M hC hD hY hM d
  · intro x hx
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌) x) at hx
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst] at hx
    exact dgGluingNativeDInclusion_generates_kernel R C D M hC hD hY hM x hx

lemma dgGluingNativeSemiorthogonal_projection :
    (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).projection =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLeftProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst R C D M)
lemma dgGluingNativeSemiorthogonal_retraction :
    (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).retraction =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableRightProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd R C D M)

lemma dgGluingNativeSemiorthogonal_isVerdier :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgGluingNativeDInclusion R C D M hC hD hY hM)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLeftProjection R C D M hC hD) := by
  have h := (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).isVerdier
  rw [dgGluingNativeSemiorthogonal_projection] at h
  exact h

lemma dgGluingDFactor_iff_nativeSemiorthogonal_image (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left ↔
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgGluingNativeDInclusion R C D M hC hD hY hM) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactor_iff_stableLeftKernel]
  have h := (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).kernel
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
  rw [dgGluingNativeSemiorthogonal_projection] at h
  exact h

lemma dgGluingNativeSemiorthogonal_mappingSpace
    (d : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD).obj _⦋0⦌)
    (c : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((dgGluingNativeDInclusion R C D M hC hD hY hM).hom.app (Opposite.op ⦋0⦌) d)
      ((dgGluingNativeCInclusion R C D M hC hD hY hM).hom.app (Opposite.op ⦋0⦌) c)) :=
  (dgGluingNativeSemiorthogonal R C D M hC hD hY hM).semiorthogonal d c

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Eq (7)" (partial := component) "仮定：安定 dg gluing と native lax の提示（Lean が強い）。結論：二因子の片方を核とする半直交分解・Verdier 列。与えた生成集合 S,T の合併で生成する一般命題を直接は述べない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeSemiorthogonal_isVerdier
attribute [cite LT "Lemma 1.9" (partial := component) "仮定：安定 dg gluing と native lax の提示（Lean が強い）。結論：二因子の片方を核とする半直交分解・Verdier 列。与えた生成集合 S,T の合併で生成する一般命題を直接は述べない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeSemiorthogonal_isVerdier
