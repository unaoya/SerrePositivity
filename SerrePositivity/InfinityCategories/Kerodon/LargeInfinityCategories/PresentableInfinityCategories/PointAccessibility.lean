module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PullbackFilteredColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedConstantColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.InitialCompact
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.TerminalFiltered

/-!
概要：点の accessibility と、任意の固定頂点への関手の filtered 保存を構成する。
方針：点への射の一意性と弱可縮形状上の定値余極限を使う。
規約：固定頂点への脚に全小余極限保存を要求しない。
使われ方：accessible 引き戻しの第二脚を点に特殊化する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：点の任意の頂点は始対象。
方針：全境界への延長を点への唯一の射で与える。
規約：元の頂点を保持する。
使われ方：点内での compact 性。 -/
lemma point_vertex_isInitial (x : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  intro n b _
  exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- 概要：点の任意の頂点は終対象。
方針：境界を点への唯一の射で延長する。
規約：追加の構造を仮定しない。
使われ方：点を任意の κ-filtered 添字として使う。 -/
lemma point_vertex_isTerminal (x : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n b _
  exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- 概要：点を標的とする元の全余錐は余極限。
方針：coslice 射影の同型を使い、境界を点から戻す。
規約：添字の弱可縮性も非空性も要求しない。
使われ方：点の余完備性と filtered 生成表示。 -/
lemma point_cocone_isColimit {K : SSet.{u}} {F : K ⟶ (Δ[0] : SSet.{u})}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceUnder_point_projection_isIso F
  intro n b _
  refine ⟨stdSimplex.isTerminalObj₀.from _ ≫ inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F), ?_⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：点は任意の小さい形状の余極限を持つ。
方針：点への唯一の全余錐を使う。
規約：元の宇宙 u+1 の点を標的とする。
使われ方：点の presentable 性。 -/
lemma point_hasSmallColimits : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (Δ[0] : SSet.{u + 1}) := by
  intro K F
  exact ⟨⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩,
    point_cocone_isColimit _⟩

/-- 概要：点は任意の正則 κ で accessible。
方針：小さい点自身を生成圏とし、一点添字の表示を取る。
規約：添字と生成圏は u、標的は u+1。
使われ方：accessible cospan の第二始域を点にする。 -/
lemma point_isKappaAccessible (κ : Cardinal.{u}) (hκ : κ.IsRegular) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ (Δ[0] : SSet.{u + 1}) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom
  refine ⟨hκ, point_hasSmallColimits.hasSmallKappaFilteredColimits κ,
    Δ[0], inferInstance, i, ?_, ?_, ?_⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0)).isQCatEquivalence.isFullyFaithful
  · intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_of_isInitialVertex hκ.aleph0_le (point_vertex_isInitial _)
  · intro x
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (Δ[0] : SSet.{u}) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex κ (point_vertex_isTerminal
        (stdSimplex.obj₀Equiv.symm 0))
    let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map (𝟙 (Δ[0] : SSet.{u})) ≫ i) :=
      ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    refine ⟨Δ[0], inferInstance, inferInstance, 𝟙 _, c, ?_, point_cocone_isColimit c⟩
    apply SSet.yonedaEquiv.symm.injective
    exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：元の点は presentable。
方針：ℵ₀-accessibility と点の全小余極限を合わせる。
規約：局所化や引き戻しの定理を使わない。
使われ方：点を含む presentable cospan。 -/
lemma point_isPresentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (Δ[0] : SSet.{u + 1}) :=
  ⟨(point_isKappaAccessible Cardinal.aleph0 Cardinal.isRegular_aleph0).isAccessible,
    point_hasSmallColimits⟩

/-- 概要：任意の定値関手は正則 κ の filtered 余極限を保存する。
方針：κ-filtered 添字の弱可縮性による定値余極限を使う。
規約：定値関手に全小余極限保存を要求しない。
使われ方：固定標的の fiber の第二脚。 -/
lemma constant_isKappaAccessibleFunctor {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {X Y : SSet.{u + 1}} [Quasicategory Y] (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (SSet.const y : X ⟶ Y) := by
  intro I hI hFiltered D c _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le I
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone_isColimit_of_pointCofinal
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.pointProjection_ulift_isRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity I)) y
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (SSet.comp_const _ _)).mpr hc

/-- 概要：任意の点射は正則 κ の filtered 余極限を保存する。
方針：Yoneda の点射を同じ頂点の定値射と同定する。
規約：標的の頂点は任意でよい。
使われ方：固定標的 fiber を accessible 引き戻しへ渡す。 -/
lemma pointMap_isKappaAccessibleFunctor {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {Y : SSet.{u + 1}} [Quasicategory Y] (x : (Δ[0] : SSet.{u + 1}) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ x := by
  have hx : x = SSet.const (SSet.yonedaEquiv x) := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_const]
  rw [hx]
  exact constant_isKappaAccessibleFunctor hκ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
