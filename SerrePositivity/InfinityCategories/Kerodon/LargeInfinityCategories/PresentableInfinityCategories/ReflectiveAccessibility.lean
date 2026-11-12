module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleFamilySaturationModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent

/-!
概要：一般の元の accessible 圏の反射的全部分圏に小さい compact 生成表示を構成する。
方針：反射した生成族の周囲での同型飽和を縮小し、その同じ模型を全部分圏へ持ち上げる。
規約：元の全部分圏に固定頂点写像の厳密な小ささを要求しない。
使われ方：局所対象圏の条件付き反射からの accessibility。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：filtered 保存の反射的包含を持つ全部分圏は同じ濃度で accessible。
方針：周囲の小さい生成族を反射し、その同型飽和の小模型へ全生成表示を移す。
規約：全部分圏の元の単体集合を使用し、accessibility 自体を入力にしない。
使われ方：条件付き局所置換反射からの局所対象圏の生成表示。 -/
lemma reflectiveSubcategory_isKappaAccessible {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {P : C _⦋0⦌ → Prop}
    (hP : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (P x ↔ P y))
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory C P) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P : SSet.{u + 1}) := by
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).ι
  let L := r.reflector
  have hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful R := r.inclusion_fullyFaithful
  obtain ⟨hκ, _, A, hA, i, hi⟩ := hC
  have := hA
  let v : A _⦋0⦌ → C _⦋0⦌ := fun t ↦ R.app _ (L.app _ (i.app _ (ULift.up t)))
  have hacc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C :=
    ⟨κ, hκ, hcol.hasSmallKappaFilteredColimits κ, A, hA, i, hi⟩
  obtain ⟨B, hB, ⟨e⟩⟩ := hacc.exists_smallFamilySaturationModel v
  have := hB
  have hv : ∀ z, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v z → P z := by
    rintro z ⟨t, ⟨hz⟩⟩
    exact (hP hz).mpr (r.localization_mem (i.app _ (ULift.up t)))
  let j := e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion v
  let jD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P j (fun b ↦ hv _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (e.hom.app _ b)))
  have hj : jD ≫ R = j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hjff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful jD := by
    apply hff.cancel_right
    rw [hj]
    exact e.isQCatEquivalence.isFullyFaithful.comp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v))
  have hdcol := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits r hcol
  refine ⟨hκ, hdcol.hasSmallKappaFilteredColimits κ, B, hB, jD, hjff, ?_, ?_⟩
  · intro b
    obtain ⟨t, ⟨ht⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (e.hom.app _ (ULift.up b))
    have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (R.app _ (jD.app _ (ULift.up b)))
        (R.app _ (L.app _ (i.app _ (ULift.up t)))) := ht
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (hff.preimageVertexIso ht')).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image r.adjunction hR (hi.compact t))
  · intro x
    obtain ⟨K, hK, hκK, a, c, hc, hpres⟩ := hi.presentation (R.app _ x)
    have := hK
    have := hκK
    let G := ((SSet.uliftFunctor.{u + 1, u}).map a ≫ i) ≫ L
    let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L c
    have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction r.adjunction c hpres
    have hdv : d.vertex = L.app _ (R.app _ x) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hc]
    obtain ⟨d', hd', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso d hd
      (eqToIso (congrArg HomotopyCategory.mk hdv) ≪≫ r.counitIso.app x)
    let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v) (G ≫ R) (by
      rintro ⟨k⟩
      exact ⟨a.app _ k, ⟨Iso.refl _⟩⟩)
    let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (H ≫ e.inv)
    have hb : (SSet.uliftFunctor.{u + 1, u}).map b = H ≫ e.inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (((SSet.uliftFunctor.{u + 1, u}).map b ≫ jD) ≫ R) (G ≫ R) := by
      rw [Category.assoc, hj, hb]
      have hh := (e.invHomIso.precomp H).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion v)
      simpa only [j, Category.assoc, Category.id_comp, H,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using hh
    have heD := hff.preimageFunctorIso he
    obtain ⟨d'', hd'', hv''⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex heD.symm d' hd'
    exact ⟨K, hK, hκK, b, d'', hv''.trans hv', hd''⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
