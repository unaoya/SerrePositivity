module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeUnitHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FlipConstantFunctorHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ParameterUnitHom

/-!
概要：転置した Hom 公式を普遍余錐へ照合して Hom 全単射を得る。
方針：頂点表示と変数交換の二つの同値で普遍余錐の全単射を輸送する。
規約：余極限関手の具体的な選択に依存しない。
使われ方：選んだ余極限単位の全パラメータ判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：転置した Hom 公式が普遍余錐の単位公式なら元の Hom 写像は全単射。
方針：二つの同値で両端を輸送し、元の余錐の全単射を適用する。
規約：同じ全余錐と指定写像を保つ。
使われ方：余極限関手の随伴の単位判定。 -/
lemma colimitUnitHom_bijective_of_flip {K A X : SSet.{u}} [Quasicategory X]
    {U : A ⟶ (ihom K).obj X} {L V : A ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K X U)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hL : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)
    (f : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom L V → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))
    (hf : ∀ α, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flip_postcompose_constant V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv U (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) (f α)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeUnitHom c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (eqToHom (congrArg HomotopyCategory.mk hL) ≫ α)) :
    Function.Bijective f := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv U (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flip_postcompose_constant V))
  let a := Iso.homCongr (eqToIso (congrArg HomotopyCategory.mk hL)).symm
    (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)))
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeUnitHom_bijective c hc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)).comp a.bijective
  have h : Function.Bijective (e ∘ f) := by
    convert hb using 1
    funext α
    simpa only [e, a, Function.comp_apply, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, eqToIso.hom, Iso.refl_hom, Category.comp_id] using hf α
  exact h.of_comp_left e.injective

/-- 概要：任意パラメータ版の単位 Hom 全単射と quasicategory 版は同値。
方針：指定写像の点ごとの一致を使う。
規約：同じ単位を保持する。
使われ方：普遍余錐から随伴の単位判定へ移す。 -/
lemma parameterUnitHomMap_bijective_iff {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap η U V) ↔
      Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η U V) := by
  have h := funext (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_eq η U V)
  rw [h]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
