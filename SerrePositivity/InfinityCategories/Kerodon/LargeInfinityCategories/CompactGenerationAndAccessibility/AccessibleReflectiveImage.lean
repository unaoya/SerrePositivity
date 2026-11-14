module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AdjunctionHomPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeUniverseContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport

/-!
概要：κ-filtered 余極限を保つ反映包含の像に小さい compact 生成圏を構成する。
方針：元の生成圏を左随伴で送り、全随伴の Hom 比較と小さい全部分模型を使う。
規約：随伴関手定理や指定宇宙変更の充満忠実性は使わない。
使われ方：関手圏と積の presentable 性を既存の反映から構成する。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：κ-filtered 保存の右随伴を持つ左随伴は κ-compact 対象を保つ。
方針：右随伴との Hom 合成の保存を全自然な随伴同型で戻す。
規約：元の濃度と元の対象を保持する。
使われ方：反映した生成対象の compact 性。 -/
lemma adjunction_isKappaCompact_image {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ R) {x : C _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (L.app (Opposite.op ⦋0⦌) x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_hom_preservesKappaFilteredColimits_iff a κ x).mp (hR.comp_universe hx)

/-- 概要：元の反映像の κ-accessibility を小さい生成圏から構成する。
方針：元の生成対象を左随伴で送り、余単位で全表示の頂点を回収する。
規約：標的の固定頂点写像の小ささと余完備性を明示し、accessibility 自体は構成する。
使われ方：反映された関手圏の presentable 性。 -/
lemma reflectiveImage_isKappaAccessible {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ L) (𝟙 D)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D) (hsD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps D)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ D := by
  obtain ⟨hκ, _, A, hA, i, hi⟩ := hC
  have := hA
  let v : A _⦋0⦌ → D _⦋0⦌ := fun t ↦ L.app _ (i.app _ (ULift.up t))
  refine ⟨hκ, hD.hasSmallKappaFilteredColimits κ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel hsD v,
    inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hsD v, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isKappaCompactGenerating hsD v
  · intro t
    exact adjunction_isKappaCompact_image a hR (hi.compact t)
  · intro x
    obtain ⟨I, hI, hκI, f, c, hc, hcol⟩ := hi.presentation (R.app _ x)
    have := hI
    have := hκI
    let G := ((SSet.uliftFunctor.{u + 1, u}).map f ≫ i) ≫ L
    let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L c
    have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction a c hcol
    have hv : d.vertex = L.app _ (R.app _ x) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hc]
    obtain ⟨d', hd', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso d hd
      (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ e.app x)
    refine ⟨I, hI, hκI, G, ?_, d', hd', hv'⟩
    intro k
    exact ⟨f.app _ k, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.1.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image
attribute [cite HTT "5.5.7.2" (partial := direction) "仮定：κ-filtered 余極限を持つ準圏の指定随伴 L⊣R と κ-continuous な R（HTT と一致）。結論：L が同じ κ-compact 対象を κ-compact に送る (1)（一致）。C が κ-accessible のときの逆方向 (2) は、この全般性の公開型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image
attribute [cite HTT "5.5.7.3" (partial := stronger-hyp) "仮定：κ-compactly generated C の指定反射 L⊣R（Lean が強い：包含 R の κ-continuity、反射像の全小余極限と固定頂点写像の小ささを明示）。結論：同じ反射像の κ-accessibility、仮定した余完備性と合わせ κ-compact generation という (4)（一致）。L 自身の κ-continuity との iff や retract の特徴づけは結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.reflectiveImage_isKappaAccessible
