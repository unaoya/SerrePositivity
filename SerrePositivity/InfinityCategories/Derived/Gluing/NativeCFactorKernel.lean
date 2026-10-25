module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalStableStructure
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (hY : IsExactFunctor (dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingNativeCInclusion_right_iso :
    FunctorIso
      ((dgGluingNativeCInclusion R C D M hC hD hY hM).hom ≫
        dgGluingUniverseRightNerve R C D M)
      ((dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom ≫
        F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (dgGluingUniverseDerivedCoefficient R C D M)) := by
  have hi := ((dgGluingUniverseDerivedNerveLaxEquivalence R C D M).invHomIso.precomp
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom).postcomp
      (F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
  simpa only [Category.assoc, dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    dgGluingUniverseDerivedNerveLaxComparison_snd, Category.id_comp, Category.comp_id,
    dgGluingNativeCInclusion, dgGluingStableComparisonInverse, Category.assoc] using! hi

lemma dgGluingNativeCInclusion_killed (c : (dgGluingStableInput.{u, v, w} R C hC).obj _⦋0⦌) :
    IsZeroVertex (((dgGluingNativeCInclusion R C D M hC hD hY hM).hom ≫
      dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) c) := by
  let p := dgGluingStableYonedaMap R C hC hY
  let q := dgGluingStableCoefficientMap R C D M hD hM
  have hz : IsZeroVertex ((LaxInclusion.fromC p q ≫ (laxSnd p q).hom).app
      (Opposite.op ⦋0⦌) c) := by
    rw [LaxInclusion.fromC_snd, LaxInclusion.zeroD, zeroDiagram_const_vertex]
    exact (chosenZeroVertex _).isZero
  exact hz.of_vertexIso ((dgGluingNativeCInclusion_right_iso R C D M hC hD hY hM).app c).symm

lemma dgGluingNativeCInclusion_generates_kernel
    (x : (dgGluingStableObject R C D M hC hD).obj _⦋0⦌)
    (hx : IsZeroVertex ((dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) x)) :
    x ∈ essentialImage (dgGluingNativeCInclusion R C D M hC hD hY hM) := by
  let p := dgGluingStableYonedaMap R C hC hY
  let q := dgGluingStableCoefficientMap R C D M hD hM
  have hz : IsZeroVertex ((F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌) x)) := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M) (Opposite.op ⦋0⦌)) x
    exact he.symm ▸ hx
  obtain ⟨c, ⟨hc⟩⟩ := (LaxInclusion.snd_kernel p q _).mp hz
  refine ⟨c, ⟨?_⟩⟩
  exact (VertexIso.map hc (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv) ≪≫
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).homInvIso.app x

lemma dgGluingNativeCInclusion_kernel
    (x : (dgGluingStableObject R C D M hC hD).obj _⦋0⦌) :
    IsZeroVertex ((dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ essentialImage (dgGluingNativeCInclusion R C D M hC hD hY hM) := by
  constructor
  · exact dgGluingNativeCInclusion_generates_kernel R C D M hC hD hY hM x
  · rintro ⟨c, ⟨hc⟩⟩
    exact (dgGluingNativeCInclusion_killed R C D M hC hD hY hM c).of_vertexIso
      (VertexIso.map hc (dgGluingUniverseRightNerve R C D M))

lemma dgGluingCanonicalCFactor_iff_image (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R D X.right ↔
      ULift.up (Simplex.vertex X) ∈
        essentialImage (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).rightInclusion := by
  rw [dgGluingCFactor_iff_stableRightKernel]
  exact dgGluingNativeCInclusion_kernel R C D M hC hD
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) _

lemma dgGluingCanonicalDFactor_iff_image (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R C X.left ↔
      ULift.up (Simplex.vertex X) ∈
        essentialImage (dgGluingCanonicalNativeSemiorthogonal R C D M hC hD).inclusion :=
  dgGluingDFactor_iff_nativeSemiorthogonal_image R C D M hC hD
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD) X

end SerrePositivity.InfinityCategories
