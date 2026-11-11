module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeExtensionFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FunctorVertex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FunctorHomCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily

/-!
概要：錐の nerve を join の形の関手単体集合へ写し固定図式を照合する。
方針：指数比較と前合成の自然性を使う。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：通常の定値関手の nerve は元の頂点への定値な射。
方針：合成可能射列への両方の作用を比較する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveMap_const (A : Type u) [Category.{u} A] (x : C) :
    nerveMap ((Functor.const A).obj x) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：通常の錐の nerve を join の形の関手単体集合へ写す。
方針：拡張関手の指数比較と join の同型による前合成を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def nerveConeFamilyUnderlying : nerve (Cone F) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve I))).obj (nerve C) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneExtensionFunctor (F := F)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso (WithInitial I) C).hom ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom).app (nerve C)

/-- 概要：関手単体集合への比較射は元の図式を全ての単体で固定する。
方針：指数比較の前合成の自然性と通常の制限の式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeFamilyUnderlying_fixed : nerveConeFamilyUnderlying (F := F) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (nerve I) (nerve C) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F)) := by
  have hp : (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom).app (nerve C) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve I))).app (nerve C) =
        (pre (nerveMap (WithInitial.incl : I ⥤ WithInitial I))).app (nerve C) := by
    rw [← NatTrans.comp_app, ← pre_map]
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap I
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom = _ at he
    rw [he]
  dsimp only [nerveConeFamilyUnderlying, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction]
  simp only [Category.assoc]
  rw [hp]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorCategoryIso_precomp (WithInitial.incl : I ⥤ WithInitial I)]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneExtensionFunctor (F := F) ⋙
    (Functor.whiskeringLeft I (WithInitial I) C).obj WithInitial.incl) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneExtensionFunctor_restrict, nerveMap_const, SSet.const_comp]
  change SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C).hom.app _
    (ComposableArrows.mk₀ F)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorCategoryIso_vertex]

/-- 概要：比較射の関手頂点は元の指定された join の錐を表す。
方針：関手頂点の指数比較の公式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeFamilyUnderlying_vertex (c : Cone F) :
    (nerveConeFamilyUnderlying (F := F)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).val := by
  simp only [nerveConeFamilyUnderlying, NatTrans.comp_app_apply, nerveMap_app_mk₀]
  change ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom).app (nerve C)).app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso (WithInitial I) C).hom.app _
      (ComposableArrows.mk₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorCategoryIso_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c)]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
