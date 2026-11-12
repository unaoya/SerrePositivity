module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightRelativeUniverse
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightBigRelativePrefix

/-!
概要：正本の小さい切断同値を、元の大きい相対写像空間の比較と厳密に結ぶ。
方針：同じ相対切断同型の逆と宇宙同型を合成し、元の因子分解で往復を相殺する。
規約：同値の順射を別の代表へ取り替えない。
使われ方：G8 の四角形①を、元の sectionsEquivalenceNatural の四角形へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] (X : I ⥤ Type u)
  (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})

/-- 正本の小さい切断表示から、元の大きい相対写像空間への指定同型。 -/
def setWeightSectionsBigRelativeIso :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (coherentSpaceSectionsObject (SetWeight.diagram X G)).obj ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (setWeightRelativeSectionsIso X G).symm ≪≫
    setWeightRelativeUniverseIso X G

/-- 元の切断同値の順射を指定相対表示へ送ると、元の大きい相対比較そのものになる。 -/
lemma setWeightSectionsEquivalenceNatural_bigRelative :
    (SetWeight.sectionsEquivalenceNatural X G).hom ≫ (setWeightSectionsBigRelativeIso X G).hom =
      setWeightBigRelativePrefix X G := by
  rw [setWeightSectionsEquivalenceNatural_hom_factor]
  simp only [setWeightSectionsBigRelativeIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  have hcancel : (SSet.uliftFunctor.{u + 1, u}).map (setWeightRelativeSectionsIso X G).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (setWeightRelativeSectionsIso X G).inv = 𝟙 _ :=
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (setWeightRelativeSectionsIso X G)).hom_inv_id
  rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (setWeightRelativeSectionsIso X G).hom),
    hcancel, Category.id_comp, setWeightRelativeUniverse_pre, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
