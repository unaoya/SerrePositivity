module
public import SerrePositivity.KST.NonConnective.DGKInputIndMorita

/-!
概要：元の全 native 族から得た実 Indω 射の恒等・二項合成を照合する。
方針：元の固定 ν の厳密保存則と Yoneda 制限比較を、保存関手の充満忠実制限で反映する。
規約：同じ実 Ind 射を保持する。全高次合成整合と懸垂構造辺の自然性は別工程。
使われ方：K-7 d4 の固定 ν・compact 生成元・実 Indω 作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] {A B C : PerfDGInput.{u, v} R}

/-- 元の全 native 族の指定頂点の Ind 作用は、同じ固定 ν 射へ Yoneda 上で比較される。 -/
def dgKInputIndNativeMap_restrictionIso (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫
      dgKInputIndNativeMap R A B f)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgKInputNuMap R f).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj) := by
  rw [dgKInputIndNativeMap_eq_extension]
  exact dgKInputIndExtension_restrictionIso R A B _

/-- 同じ元の恒等 dg 射の実 Ind 作用は恒等関手と比較される。 -/
def dgKInputIndNativeMap_idIso (A : PerfDGInput.{u, v} R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputIndNativeMap R A A (𝟙 A)) (𝟙 _) := by
  have hν : (dgKInputNuMap R (𝟙 A)).hom = 𝟙 (dgKInputStableValue R A).obj := by
    rw [dgKInputNuMap_eq]
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R A) (dgKInputStableValue R A) => f.hom)
      ((presentedPerfectDGStableCategoryFunctor R).map_id A)
  apply dgKInputIndFunctorIso_of_restriction R A A _ _
    (dgKInputIndNativeMap_preservesFilteredColimits R A A (𝟙 A))
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits Cardinal.aleph0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence)
  simpa only [hν, Functor.map_id, Category.id_comp, Category.comp_id] using!
    dgKInputIndNativeMap_restrictionIso R (𝟙 A)

/-- 元の二つの厳密 dg 射の実 Ind 作用の合成は、同じ元の合成射の作用と比較される。 -/
def dgKInputIndNativeMap_compIso (f : A ⟶ B) (g : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputIndNativeMap R A B f ≫ dgKInputIndNativeMap R B C g)
      (dgKInputIndNativeMap R A C (f ≫ g)) := by
  have hν : (dgKInputNuMap R (f ≫ g)).hom =
      (dgKInputNuMap R f).hom ≫ (dgKInputNuMap R g).hom := by
    rw [dgKInputNuMap_eq, dgKInputNuMap_eq, dgKInputNuMap_eq]
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R A) (dgKInputStableValue R C) => f.hom)
      ((presentedPerfectDGStableCategoryFunctor R).map_comp f g)
  let F := dgKInputIndNativeMap R A B f
  let G := dgKInputIndNativeMap R B C g
  let fν := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgKInputNuMap R f).hom
  have e₁ := (dgKInputIndNativeMap_restrictionIso R f).postcomp G
  have e₂ := (dgKInputIndNativeMap_restrictionIso R g).precomp fν
  have e₃ := (dgKInputIndNativeMap_restrictionIso R (f ≫ g)).symm
  apply dgKInputIndFunctorIso_of_restriction R A C _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallFilteredColimits_comp
      (dgKInputIndNativeMap_preservesFilteredColimits R A B f)
      (dgKInputIndNativeMap_preservesFilteredColimits R B C g))
    (dgKInputIndNativeMap_preservesFilteredColimits R A C (f ≫ g))
  have e₁' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫ (F ≫ G))
      (fν ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj ≫ G) := by
    simpa only [Category.assoc] using! e₁
  have e₃' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (fν ≫ (SSet.uliftFunctor.map (dgKInputNuMap R g).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R C).obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫
        dgKInputIndNativeMap R A C (f ≫ g)) := by
    simpa only [hν, Functor.map_comp, Category.assoc, fν] using! e₃
  exact e₁' ≪≫ e₂ ≪≫ e₃'

end SerrePositivity.KST.NonConnective
