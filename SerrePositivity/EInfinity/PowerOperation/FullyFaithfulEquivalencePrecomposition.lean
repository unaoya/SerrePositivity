module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso

/-!
# 指定された同値による前合成での充満忠実性の検出

DAG XIII §2.2 の全頂点の比較の補助。同じ逆と指定二胞体を後合成する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors

lemma fullyFaithful_of_equivalence_precomposition {A B D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory D]
    (e : QCatEquivalence A B) (F : B ⟶ D) (h : IsFullyFaithful (e.hom ≫ F)) :
    IsFullyFaithful F := by
  have hc := e.symm.isFullyFaithful.comp h
  have ht : FunctorIso (e.inv ≫ (e.hom ≫ F)) F := by
    simpa only [Category.assoc, Category.id_comp] using e.invHomIso.postcomp F
  exact ht.isFullyFaithful_iff.mp hc

end SerrePositivity.EInfinity.PowerOperation
