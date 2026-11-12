module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CanonicalStableStructure
public import SerrePositivity.KST.LocalizingInvariants.LaxSecondProjectionKernel
/-!
概要：元 gluing の C 因子を、native 半直交分解の C 包含の本質像と同定する。
方針：Sp の第二射影核の公開判定を正本比較の実逆と両往復同型で戻す。
規約：元の右射影と因子の H⁰ 零性を保ち、核の生成や二脚の完全性を仮定しない。
使われ方：G-1 e の両因子の整合と、続く gluing 内の部分圏の同定に用いる。
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
def dgGluingNativeCInclusion_right_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCInclusion R C D M hC hD hY hM).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  have hi := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd, Category.id_comp, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparisonInverse, Category.assoc] using! hi

lemma dgGluingNativeCInclusion_killed (c : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCInclusion R C D M hC hD hY hM).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) c) := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC hY
  let q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD hM
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((LaxInclusion.fromC p q ≫ (laxSnd p q).hom).app
      (Opposite.op ⦋0⦌) c) := by
    rw [LaxInclusion.fromC_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex _).isZero
  exact hz.of_vertexIso ((dgGluingNativeCInclusion_right_iso R C D M hC hD hY hM).app c).symm

lemma dgGluingNativeCInclusion_generates_kernel
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD).obj _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) x)) :
    x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCInclusion R C D M hC hD hY hM) := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC hY
  let q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD hM
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌) x)) := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd R C D M) (Opposite.op ⦋0⦌)) x
    exact he.symm ▸ hx
  obtain ⟨c, ⟨hc⟩⟩ := (LaxInclusion.snd_kernel p q _).mp hz
  refine ⟨c, ⟨?_⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).homInvIso.app x

lemma dgGluingNativeCInclusion_kernel
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCInclusion R C D M hC hD hY hM) := by
  constructor
  · exact dgGluingNativeCInclusion_generates_kernel R C D M hC hD hY hM x
  · rintro ⟨c, ⟨hc⟩⟩
    exact (dgGluingNativeCInclusion_killed R C D M hC hD hY hM c).of_vertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M))

lemma dgGluingCanonicalCFactor_iff_image (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D X.right ↔
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).rightInclusion := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactor_iff_stableRightKernel]
  exact dgGluingNativeCInclusion_kernel R C D M hC hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) _

lemma dgGluingCanonicalDFactor_iff_image (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left ↔
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).inclusion :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactor_iff_nativeSemiorthogonal_image R C D M hC hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) X

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
