module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleRelativeModel
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNervePrecomposition
public import SerrePositivity.EInfinity.Hammock.RelativeEquivalenceWeak

/-!
# 元の通常加群相対圏の局所化普遍性

概要：M10/C02 の元の通常加群圏の全標的普遍性をモデルの既存定理から移す。
方針：同じ宇宙表示の同値の弱単位・余単位と既存の源移送を使う。
規約：HA §1.3.4、元の自由 DK 局所化と擬同型を保持する。
使われ方：半自由 dg nerve との同じ指定源の比較。
注意：strictRawModuleSource の半自由標的への普遍性は別の比較として残る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 概要：元の表示の往復の同じ逆単位は元の弱射。
方針：同じ自然同型を Hom の持ち上げを戻して評価する。
規約：HA §1.3.4、全対象。使われ方：既存の源移送の弱変形。 -/
lemma strictRawModuleUniverseUnit_weak (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleRelativeCategory A X).weakEquivalences
      ((strictRawModuleUniverseEquivalence A X).unitIso.inv.app M) := by
  intro x
  change QuasiIso ((moduleEvaluation A (dgAlgebraCategory A ((assocForget A).obj X)) x).map
    ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).map
      ((strictRawModuleUniverseEquivalence A X).unitIso.inv.app M)))
  infer_instance

/-- 概要：モデル表示の往復の同じ余単位はモデルの元の弱射。
方針：同じ自然同型の像は同型なので構成済みモデルの弱同値。
規約：HA §1.3.4、元の全モデル。使われ方：源移送の他方の弱変形。 -/
lemma strictRawModuleUniverseCounit_weak (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    ∀ M : (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category,
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).weakEquivalences
          ((strictRawModuleUniverseEquivalence A X).counitIso.hom.app M) := by
  let := strictRawModuleModelCategory A X
  dsimp only
  intro M
  change weakEquivalences (strictRawModuleCategory A X)
    (AsSmall.down.map ((strictRawModuleUniverseEquivalence A X).counitIso.hom.app M))
  exact (_root_.HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance

/-- 概要：同じ宇宙表示の比較は全 hammock nerve の同値。
方針：既存の弱単位・余単位の実 Hom 比較を全 nerve 判定へ渡す。
規約：HA §1.3.4、同じ実相対関手。使われ方：元の DK 標的への復帰。 -/
lemma strictRawModuleHammockUniverse_isQCatEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (strictRawModuleToModelRelative A X)) := by
  let := strictRawModuleModelCategory A X
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_isQCatEquivalence_of_counit
    (strictRawModuleToModelRelative A X) (strictRawModuleFromModelRelative A X)
    (strictRawModuleUniverseEquivalence A X).counitIso.hom
    (strictRawModuleUniverseCounit_weak A X)
    (Hammock.RelativeEquivalence.colimitMap_weak
      (strictRawModuleToModelRelative A X) (strictRawModuleFromModelRelative A X)
      (strictRawModuleUniverseEquivalence A X).unitIso.inv (strictRawModuleUniverseUnit_weak A X)
      (strictRawModuleUniverseEquivalence A X).counitIso.hom
      (strictRawModuleUniverseCounit_weak A X))

/-- 概要：同じ元の全加群相対圏の hammock は全標的の局所化。
方針：同じ弱変形による源移送の後、同じ hammock 比較の標的同値を外す。
規約：HA §1.3.4、元の弱辺集合。使われ方：元の自由 DK 源の普遍性。 -/
lemma strictRawModuleHammock_isLocalization (X : (operad A).Algebra) :
    IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (strictRawModuleRelativeCategory A X))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (strictRawModuleRelativeCategory A X)) := by
  let := strictRawModuleModelCategory A X
  have h := isLocalization_of_weakDeformation
    (nerveMap (strictRawModuleFromModelRelative A X).functor)
    (nerveMap (strictRawModuleToModelRelative A X).functor)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (strictRawModuleRelativeCategory A X))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_mapsWeak (strictRawModuleFromModelRelative A X))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_mapsWeak (strictRawModuleToModelRelative A X))
    (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
      (strictRawModuleUniverseEquivalence A X).unitIso.inv)
    (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
      (strictRawModuleUniverseEquivalence A X).counitIso.hom)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_homotopy_component_weak _ (strictRawModuleUniverseUnit_weak A X))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_homotopy_component_weak _ (strictRawModuleUniverseCounit_weak A X))
    (strictRawModuleModelHammock_isLocalization A X)
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_source] at h
  exact (isLocalization_comp_equivalence_iff _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_inverts (strictRawModuleRelativeCategory A X))
    (strictRawModuleHammockUniverse_isQCatEquivalence A X).choose).mp h

/-- 概要：同じ元の通常加群圏の自由 DK 源は全標的の局所化。
方針：既存の同じ hammock との標的同値の普遍性判定を使う。
規約：HA §1.3.4、半自由標的への別の源とは区別。
使われ方：M10/C02 の元の固定底の普遍性。 -/
lemma strictRawModuleLocalization_isLocalization (X : (operad A).Algebra) :
    IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A X))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (strictRawModuleRelativeCategory A X)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_isLocalization_iff (strictRawModuleRelativeCategory A X)).mpr
    (strictRawModuleHammock_isLocalization A X)

end SerrePositivity.EInfinity.BarrattEccles
