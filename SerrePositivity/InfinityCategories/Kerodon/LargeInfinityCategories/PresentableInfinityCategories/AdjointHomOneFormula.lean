module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionParameter

/-!
概要：Hom₁ の逆対応を元の単位による Hom の合成として表示する。
方針：QCat の厳密な単位子・結合子を相殺し、二つの whisker を表示する。
規約：元の全関手圏の単位と指定 Hom を保持する。
使われ方：前合成の随伴単位の恒等関手での成分の回収。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance adjointHomOneFormulaCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：恒等の単体写像が h に誘導する射作用は恒等。
方針：hoFunctor の恒等保存を元の射へ適用する。
規約：元のホモトピー圏の射を保持する。
使われ方：単位成分の恒等作用の簡約。 -/
lemma hoFunctor_map_id_apply {E : SSet.{u}} {x y : hoFunctor.obj E} (α : x ⟶ y) :
    (hoFunctor.map (𝟙 E)).toFunctor.map α = α := by
  have h := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (hoFunctor.map_id E)) α
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Cat.Hom.id_map] using h

/-- 概要：Hom₁ 逆対応は単位の後合成と指定 Hom の前合成の合成。
方針：双圏の単位による公式を、元の h Fun の二つの関手作用で表示する。
規約：U と V は任意の元の関手。
使われ方：前合成の随伴単位の成分を元の単位へ照合する。 -/
lemma adjointHomOneEquiv_formula {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (U : C ⟶ E) (V : D ⟶ E) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a U V α =
      (hoFunctor.map ((ihom C).map U)).toFunctor.map a.unitHom ≫
        (hoFunctor.map ((pre L).app E)).toFunctor.map α := by
  let α' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U) V).symm α
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight a.unit U
  have hα := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft L α'
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U (L ≫ V))
    (Bicategory.Adjunction.homEquiv₁_symm_apply a α')
  simp only [Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a U V α =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (a.unit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L ◁ α') at h
  exact h.trans (congrArg₂ (· ≫ ·) hu hα)

/-- 概要：恒等関手の Hom₁ 逆対応で右随伴の恒等 Hom を移すと元の単位。
方針：単位の公式で二つの恒等の関手作用を相殺する。
規約：元の h Fun(C,C) の単位を保持する。
使われ方：前合成の随伴単位の恒等関手での成分の回収。 -/
lemma adjointHomOneEquiv_identity {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a (𝟙 C) R (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R))) = a.unitHom := by
  have h := adjointHomOneEquiv_formula a (𝟙 C) R
    (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R)))
  have hp := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) ((ihom C).map_id C)) a.unitHom
  have hp' : (hoFunctor.map ((ihom C).map (𝟙 C))).toFunctor.map a.unitHom = a.unitHom := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, hoFunctor_map_id_apply] using hp
  have hi := (hoFunctor.map ((pre L).app C)).toFunctor.map_id
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R))
  exact h.trans ((congrArg₂ (· ≫ ·) hp' hi).trans (Category.comp_id _))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
