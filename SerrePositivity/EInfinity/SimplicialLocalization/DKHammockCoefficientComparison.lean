module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMapAugmentation
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMapComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalReductionWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalComparisonWeak
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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel

def dkHammockComparisonIso (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (Hammock.reducedSimplicialSet C.weakEquivalences X Y) := by
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalReduction C X Y)
    (freeHammockDiagonalReduction_isWeakHomotopyEquivalence C X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (freeHammockDiagonalComparison C X Y))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalReduction C X Y))

lemma dkHammockComparisonIso_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalComparison C X Y) ≫
        (dkHammockComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalReduction C X Y) := by
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

lemma dkHammockComparisonIso_coefficient {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (localizationHomMap F X Y) ≫
        (dkHammockComparisonIso D (F.functor.obj X) (F.functor.obj Y)).hom =
      (dkHammockComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (Hammock.Relative.reducedMap F X Y) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have hr := congrArg Q.map (freeHammockDiagonalMap_comparison F X Y)
  have hl := congrArg Q.map (freeHammockDiagonalMap_reduction F X Y)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, ← hr, Category.assoc, dkHammockComparisonIso_fac, hl,
    ← dkHammockComparisonIso_fac, Category.assoc]

end SerrePositivity.EInfinity.SimplicialLocalization
