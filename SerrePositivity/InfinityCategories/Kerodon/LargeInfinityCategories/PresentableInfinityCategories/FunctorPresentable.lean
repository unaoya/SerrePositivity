module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresheafModel
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndPresheafReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaSmallness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-!
概要：小さい ∞ 圏上の presentable 圏値の全関手圏が presentable であることを構成する。
方針：前層の反映 Ind 模型を全関手圏へ送り、反映生成対象から accessibility を得る。
規約：随伴関手定理の未供給比較や一般 Bousfield 局所化を使わない。
使われ方：HTT 5.5.3.6 と Pr^L の小極限の準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：κ-filtered 保存は全関手圏の後合成へ移る。
方針：元の κ-filtered 全余錐の各点計算を使う。
規約：パラメーター圏 A は任意で、濃度を変更しない。
使われ方：反映包含の後合成の accessibility。 -/
lemma functorPostcomp_isKappaAccessible {κ : Cardinal.{u}} (A : SSet.{u + 1})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C) (F : C ⟶ D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ ((ihom A).map F) := by
  intro I hI hκ p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.postcomposition_map_isColimit (hC I) F (hF I) c hc

/-- 概要：余完備な Ind 圏値の小さい全関手圏は presentable。
方針：前層値関手圏の反映と κ-filtered 保存包含から小さい compact 生成圏を構成する。
規約：元の Ind の余完備性は明示し、比較界面の未供給条件は使わない。
使われ方：一般の presentable 圏値の関手圏への同値移送。 -/
lemma functorInd_isPresentable (K A : SSet.{u}) [Quasicategory K] [Quasicategory A]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hI : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) := by
  let T := (SSet.uliftFunctor.{u + 1, u}).obj K
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indPresheafReflection hI
  have hcol := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.functor_hasSmallColimits T hI
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps ((ihom T).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) := by
    have (n : SimplexCategoryᵒᵖ) : Small.{u} (T.obj n) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (K.obj n)))
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ A).functorSpace T
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ ((ihom T).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ A)) :=
    functorPostcomp_isKappaAccessible T (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ A) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indInclusion_preservesSmallKappaFilteredColimits κ A)
  obtain ⟨μ, hκμ, hμ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorPresheaf_isPresentable K A).isAccessible.exists_larger κ
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((ihom T).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ A)) ≫
      (ihom T).map r.reflector) (𝟙 ((ihom T).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A))) := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity] using
      r.counitIso.map_post T
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.reflectiveImage_isKappaAccessible (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionAdjunction r.adjunction T)
    he hμ hcol hs (hr.of_le hκμ.le)).isAccessible, hcol⟩

/-- 概要：小さい ∞ 圏上の presentable 圏値の全関手圏は presentable。
方針：元の反映 Ind 模型の全関手圏を構成し、元の同値の後合成で戻す。
規約：K の単体は u、C の単体は u+1。
使われ方：HTT 5.5.3.6、Pr^L の積と引き戻しの準備。 -/
lemma functor_isPresentable (K : SSet.{u}) [Quasicategory K]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj C) := by
  obtain ⟨κ, hκ, A, hA, ⟨r⟩, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  have := hA
  have : Fact κ.IsRegular := ⟨hκ⟩
  have hi := hC.hasSmallColimits.of_equivalence e.symm
  exact (functorInd_isPresentable K A κ hi).of_equivalence
    (e.postcompose ((SSet.uliftFunctor.{u + 1, u}).obj K))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.4.3" (partial := stronger-hyp) "仮定：小準圏 K と presentable な C（Lean が強い：C は accessible に加えて全小余極限を持つ。K も任意の単体集合でなく準圏）。結論：元の Fun(K,C) は presentable、従って accessible（この場合に一致）。任意の accessible C や非準圏形状への比較を追加していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable
attribute [cite HTT "5.5.3.6" (partial := special) "仮定：presentable C と小準圏 K（Lean が強い：任意の小単体集合でなく準圏形状）。結論：元の Fun(K,C) が presentable（この形状の場合に一致）。非準圏形状の fibrant 模型との比較を仮定して一般化しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable
