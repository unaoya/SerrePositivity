module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization

/-! # 基本亜群の表示に使う nerve 随伴の具体的な転置
概要：任意の単体集合のホモトピー圏からの関手を nerve 値写像へ移す。
方針：既存の nerve 随伴の Hom 同値と自然性を通常の関手の型で公開する。
規約：源の quasicategory 性は不要。使われ方：Kan 置換前の辺と二単体による生成表示。

対応節は Kerodon 3.5（Tag 0513）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories

/-- 任意の単体集合のホモトピー圏からの関手を nerve 値写像に転置する。 -/
def fundamentalNerveTranspose {A : SSet.{u}} {C : Type u} [Category.{u} C]
    (F : hoFunctor.obj A ⥤ C) : A ⟶ nerve C :=
  nerveAdjunction.homEquiv A (Cat.of C) (F.toCatHom)

/-- nerve 値写像を元のホモトピー圏からの関手へ戻す。 -/
def fundamentalNerveUntranspose {A : SSet.{u}} {C : Type u} [Category.{u} C]
    (f : A ⟶ nerve C) : hoFunctor.obj A ⥤ C :=
  ((nerveAdjunction.homEquiv A (Cat.of C)).symm f).toFunctor

/-- nerve の転置を戻すと元の関手を厳密に回収する。 -/
lemma fundamentalNerveUntranspose_transpose {A : SSet.{u}} {C : Type u} [Category.{u} C]
    (F : hoFunctor.obj A ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose F) = F :=
  congrArg Cat.Hom.toFunctor ((nerveAdjunction.homEquiv A (Cat.of C)).symm_apply_apply _)

/-- 戻した関手を転置すると元の nerve 値写像を厳密に回収する。 -/
lemma fundamentalNerveTranspose_untranspose {A : SSet.{u}} {C : Type u} [Category.{u} C]
    (f : A ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose f) = f :=
  (nerveAdjunction.homEquiv A (Cat.of C)).apply_symm_apply _

/-- 転置は単体集合側の前合成を保つ。 -/
lemma fundamentalNerveTranspose_pre {A B : SSet.{u}} {C : Type u} [Category.{u} C]
    (i : A ⟶ B) (F : hoFunctor.obj B ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose ((hoFunctor.map i).toFunctor ⋙ F) =
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose F :=
  nerveAdjunction.homEquiv_naturality_left i (F.toCatHom)

/-- 戻す操作は単体集合側の前合成を保つ。 -/
lemma fundamentalNerveUntranspose_pre {A B : SSet.{u}} {C : Type u} [Category.{u} C]
    (i : A ⟶ B) (f : B ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (i ≫ f) =
      (hoFunctor.map i).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose f :=
  congrArg Cat.Hom.toFunctor (nerveAdjunction.homEquiv_naturality_left_symm (Y := Cat.of C) i f)

/-- 転置は圏側の後合成を保つ。 -/
lemma fundamentalNerveTranspose_post {A : SSet.{u}} {C D : Type u}
    [Category.{u} C] [Category.{u} D] (F : hoFunctor.obj A ⥤ C) (G : C ⥤ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (F ⋙ G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose F ≫ nerveFunctor.map (G.toCatHom) :=
  nerveAdjunction.homEquiv_naturality_right (F.toCatHom) (G.toCatHom)

/-- 戻す操作は圏側の後合成を保つ。 -/
lemma fundamentalNerveUntranspose_post {A : SSet.{u}} {C D : Type u}
    [Category.{u} C] [Category.{u} D] (f : A ⟶ nerve C) (G : C ⥤ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (f ≫ nerveFunctor.map (G.toCatHom)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose f ⋙ G :=
  congrArg Cat.Hom.toFunctor
    (nerveAdjunction.homEquiv_naturality_right_symm (Y := Cat.of C) (Y' := Cat.of D) f (G.toCatHom))

/-- 通常の亜群の nerve は追加のモデル圏仮定なしに Kan 複体となる。 -/
instance fundamentalGroupoidNerve_kanComplex (C : Type u) [Category.{u} C] [IsGroupoid C] :
    KanComplex (nerve C) := by
  let e : hoFunctor.obj (nerve C) ≌ C :=
    Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of C))
  have : IsGroupoid (hoFunctor.obj (nerve C)) := isGroupoid_of_reflects_iso e.functor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalGroupoidNerve_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalGroupoidNerve_kanComplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalGroupoidNerve_kanComplex

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveTranspose := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_post := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_pre := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose_pre

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_untranspose := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose_untranspose

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_post := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_pre := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_pre

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_transpose := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_transpose
