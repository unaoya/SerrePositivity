module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgAdjunctionComparison
public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.HomotopyRecovery
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.EdgeHom
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.EInfinity.Interface.Theory
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# 全 Barratt–Eccles 代数のホモトピー圏の局所化

## 概要
厳密な全代数の弱同値を、CAlg のホモトピー圏で反転する。

## 方針
全関手の ∞ 局所化から通常の局所化を得て、nerve の辺を元の代数射で評価する。

## 規約
代数の対象と弱同値は元の全相対圏のものを使う。

## 使われ方
H⁰ の関手とその比較を CAlg のホモトピー圏に降ろす。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories SerrePositivity.KST.LocalizingInvariants
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- ホモトピー圏から読み戻した通常の射が元の代数の弱同値であるという条件。 -/
abbrev allAlgebraNerveHoWeak :
    MorphismProperty (nerve (allAlgebraRelativeCategory A).category).HomotopyCategory :=
  (allAlgebraRelativeCategory A).weakEquivalences.inverseImage
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation (allAlgebraRelativeCategory A).category)

/-- 全厳密代数の nerve のホモトピー圏からの通常の局所化。 -/
lemma allAlgebraCAlgSource_hoIsLocalization :
    (hoFunctor.map (allAlgebraCAlgSource A)).toFunctor.IsLocalization
      (allAlgebraNerveHoWeak A) := by
  apply localizationHo_isLocalization _ _ (allAlgebraCAlgSource_isLocalization A)
  intro x y e
  obtain ⟨X, rfl⟩ := nerveEquiv.symm.surjective x
  obtain ⟨Y, rfl⟩ := nerveEquiv.symm.surjective y
  obtain ⟨g, rfl⟩ := nerve.edgeMk_surjective e
  change (allAlgebraRelativeCategory A).weakEquivalences
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation _).map (HomotopyCategory.homMk (nerve.edgeMk g))) ↔
    ComposableArrows.mk₁ g ∈ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (allAlgebraRelativeCategory A)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation_map_homMk]
  constructor
  · exact fun h => ⟨_, _, g, h, rfl⟩
  · rintro ⟨X', Y', g', hg', he⟩
    let W := (allAlgebraRelativeCategory A).weakEquivalences
    change W ((ComposableArrows.mk₁ g).hom)
    rw [he]
    exact hg'

/-- 全代数の nerve を評価し、射の宇宙を元に戻す圏同値。 -/
def allAlgebraHoEvaluation :
    (nerve (allAlgebraRelativeCategory A).category).HomotopyCategory ≌ (operad A).Algebra := by
  let C := (allAlgebraRelativeCategory A).category
  let J := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion C
  let E := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation C
  have c : J ⋙ E = 𝟭 C := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y g
    simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation_map_homMk g
  letI := Functor.IsEquivalence.mk' J
    (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation_comp_inclusion C)).symm (eqToIso c)
  exact E.asEquivalence.trans
    (ULiftHom.equiv : (operad A).Algebra ≌ ULiftHom.{u + 1} (operad A).Algebra).symm

/-- 元の厳密代数の圏からホモトピー圏への局所化源。 -/
abbrev ordinaryAlgebraHoSource :
    (operad A).Algebra ⥤ (CAlg_R A).HomotopyCategory :=
  ordinaryToHoNerve (operad A).Algebra ⋙ hoMap (algebraCAlgSource A)

/-- 射の宇宙を下げる写像は、各通常対象の頂点を同じ対象へ送る。 -/
lemma mixedNerveDown_obj (X : (allAlgebraRelativeCategory A).category) :
    (allAlgebraDownNerve A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((allAlgebraDKDown A).obj X) :=
  ComposableArrows.ext₀ rfl

/-- 射の宇宙を下げると、二つの nerve の通常の圏からの包含が可換。 -/
def allAlgebraHoDownIso :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion (allAlgebraRelativeCategory A).category ⋙
      hoMap (allAlgebraDownNerve A) ≅
    allAlgebraDKDown A ⋙ ordinaryToHoNerve (operad A).Algebra := by
  refine NatIso.ofComponents (fun X =>
    eqToIso (congrArg HomotopyCategory.mk (mixedNerveDown_obj A X))) ?_
  intro X Y g
  let D := allAlgebraDKDown A
  let e := (nerve.edgeMk g).map (allAlgebraDownNerve A)
  let e' := nerve.edgeMk (D.map g)
  have h₁ : e.edge = e'.edge := by
    change ComposableArrows.mk₁ g ⋙ D = ComposableArrows.mk₁ (D.map g)
    exact ComposableArrows.ext₁ rfl rfl (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.homMk_congr (mixedNerveDown_obj A X) (mixedNerveDown_obj A Y) e e' h₁
  let hx := congrArg HomotopyCategory.mk (mixedNerveDown_obj A X)
  let hy := congrArg HomotopyCategory.mk (mixedNerveDown_obj A Y)
  change HomotopyCategory.homMk e ≫ eqToHom hy = eqToHom hx ≫ HomotopyCategory.homMk e'
  rw [← h₂]
  simp only [← Category.assoc, eqToHom_refl, Category.id_comp]
  rfl

set_option maxHeartbeats 600000 in
-- Compare both Hom universes in the same composite functor.
/-- 全代数の nerve の評価を通すと、二つの局所化源が自然同型。 -/
def allAlgebraHoEvaluation_sourceIso :
    (allAlgebraHoEvaluation A).functor ⋙ ordinaryAlgebraHoSource A ≅
      hoMap (allAlgebraCAlgSource A) := by
  let C := (allAlgebraRelativeCategory A).category
  let E := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation C
  let J := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion C
  let D := allAlgebraDKDown A
  let B := hoMap (algebraCAlgSource A)
  let U := hoMap (allAlgebraDownNerve A)
  let I := ordinaryToHoNerve (operad A).Algebra
  have e : (allAlgebraHoEvaluation A).functor ⋙ ordinaryAlgebraHoSource A ≅
      E ⋙ D ⋙ I ⋙ B := by
    exact Iso.refl _
  have h : U ⋙ B = hoMap (allAlgebraCAlgSource A) := by
    rw [allAlgebraCAlgSource_down]
    change _ = (hoFunctor.map (allAlgebraDownNerve A ≫ algebraCAlgSource A)).toFunctor
    rw [hoFunctor.map_comp]
    rfl
  exact e ≪≫ Functor.isoWhiskerLeft E
      ((Functor.associator D I B).symm ≪≫
        Functor.isoWhiskerRight (allAlgebraHoDownIso A).symm B ≪≫ Functor.associator J U B) ≪≫
    (Functor.associator E J (U ⋙ B)).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyEvaluation_comp_inclusion C)) (U ⋙ B) ≪≫
    Functor.leftUnitor _ ≪≫ eqToIso h

/-- 元の厳密代数の圏での弱同値。 -/
abbrev ordinaryAlgebraWeak : MorphismProperty (operad A).Algebra :=
  (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))

/-- CAlg のホモトピー圏は厳密代数の弱同値による通常の局所化。 -/
lemma ordinaryAlgebraHoSource_isLocalization :
    (ordinaryAlgebraHoSource A).IsLocalization (ordinaryAlgebraWeak A) := by
  have := allAlgebraCAlgSource_hoIsLocalization A
  apply Functor.IsLocalization.of_equivalence_source (hoMap (allAlgebraCAlgSource A))
    (allAlgebraNerveHoWeak A) _ _ (allAlgebraHoEvaluation A) ?_ ?_
    (allAlgebraHoEvaluation_sourceIso A)
  · intro X Y g hg
    apply (ordinaryAlgebraWeak A).le_isoClosure
    exact hg
  · intro X Y g hg
    exact algebraCAlgSource_map_weak A g hg

end SerrePositivity.EInfinity.BarrattEccles
