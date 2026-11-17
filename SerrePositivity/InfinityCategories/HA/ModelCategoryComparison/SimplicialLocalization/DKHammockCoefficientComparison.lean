module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapAugmentation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalReductionWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalComparisonWeak
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

/-!
# DK Hom と hammock の比較同型の係数自然性

概要：元の左右弱比較の同じ span は全相対関手に自然な高次比較を与える。
方針：左右の可換式を anodyne 局所化へ送り、元の右射を消去する。
規約：元の全単体を保ち、両端点の高次自然性はここで仮定しない。
使われ方：実 DK Hom と既存 Map^h の全自然比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel

def dkHammockComparisonIso (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.EInfinity.Hammock.reducedSimplicialSet C.weakEquivalences X Y) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction_isWeakHomotopyEquivalence C X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y))

lemma dkHammockComparisonIso_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

lemma dkHammockComparisonIso_coefficient {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso D (F.functor.obj X) (F.functor.obj Y)).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.EInfinity.Hammock.Relative.reducedMap F X Y) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have hr := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_comparison F X Y)
  have hl := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_reduction F X Y)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, ← hr, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_fac, hl,
    ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_fac, Category.assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
