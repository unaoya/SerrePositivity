module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorPresheafModel
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleReflectiveImage
public import SerrePositivity.InfinityCategories.F2.Presentable.IndPresheafReflection
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSmallness
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：小さい ∞ 圏上の presentable 圏値の全関手圏が presentable であることを構成する。
方針：前層の反映 Ind 模型を全関手圏へ送り、反映生成対象から accessibility を得る。
規約：随伴関手定理の未供給比較や一般 Bousfield 局所化を使わない。
使われ方：HTT 5.5.3.6 と Pr^L の小極限の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：κ-filtered 保存は全関手圏の後合成へ移る。
方針：元の κ-filtered 全余錐の各点計算を使う。
規約：パラメーター圏 A は任意で、濃度を変更しない。
使われ方：反映包含の後合成の accessibility。 -/
lemma functorPostcomp_isKappaAccessible {κ : Cardinal.{u}} (A : SSet.{u + 1})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : Ind.HasSmallKappaFilteredColimits κ C) (F : C ⟶ D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ ((ihom A).map F) := by
  intro I hI hκ p c hc
  exact postcomposition_map_isColimit (hC I) F (hF I) c hc

/-- 概要：余完備な Ind 圏値の小さい全関手圏は presentable。
方針：前層値関手圏の反映と κ-filtered 保存包含から小さい compact 生成圏を構成する。
規約：元の Ind の余完備性は明示し、比較界面の未供給条件は使わない。
使われ方：一般の presentable 圏値の関手圏への同値移送。 -/
lemma functorInd_isPresentable (K A : SSet.{u}) [Quasicategory K] [Quasicategory A]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hI : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (Ind.IndInfinity κ A)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (Ind.IndInfinity κ A)) := by
  let T := (SSet.uliftFunctor.{u + 1, u}).obj K
  let r := indPresheafReflection hI
  have hcol := functor_hasSmallColimits T hI
  have hs : Ind.HasSmallFixedVertexMaps ((ihom T).obj (Ind.IndInfinity κ A)) := by
    have (n : SimplexCategoryᵒᵖ) : Small.{u} (T.obj n) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (K.obj n)))
    exact (Ind.ind_hasSmallFixedVertexMaps κ A).functorSpace T
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ ((ihom T).map (Ind.indInclusionPresheaf κ A)) :=
    functorPostcomp_isKappaAccessible T (Ind.ind_hasSmallKappaFilteredColimits κ A) _
      (Ind.indInclusion_preservesSmallKappaFilteredColimits κ A)
  obtain ⟨μ, hκμ, hμ⟩ := (functorPresheaf_isPresentable K A).isAccessible.exists_larger κ
  have he : FunctorIso (((ihom T).map (Ind.indInclusionPresheaf κ A)) ≫
      (ihom T).map r.reflector) (𝟙 ((ihom T).obj (Ind.IndInfinity κ A))) := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Ind.indInclusionPresheaf, Ind.IndInfinity] using
      r.counitIso.map_post T
  exact ⟨(reflectiveImage_isKappaAccessible (postcompositionAdjunction r.adjunction T)
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

end SerrePositivity.InfinityCategories.F2.Presentable
