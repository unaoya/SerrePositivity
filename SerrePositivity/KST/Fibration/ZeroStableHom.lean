module
public import SerrePositivity.KST.Fibration.ZeroStableHomFamilies

/-! # 零の安定圏を始域・標的とする元の完全関手の全写像空間 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の Kan Hom の実頂点が表す、同じ完全関手。 -/
def stableHomExactMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (v : (A ⟶[SSet.{u}] B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι.app (Opposite.op ⦋0⦌) v)

/-- 全 Hom の元の頂点は、同じ完全関手の元の関手頂点として回収される。 -/
theorem stableHomAmbient_vertex {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (v : (A ⟶[SSet.{u}] B) _⦋0⦌) :
    (stableHomAmbient A B).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableHomExactMap v).hom :=
  (congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B).apply_symm_apply
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι.app (Opposite.op ⦋0⦌) v))).symm

/-- 零標的への元の完全関手は、関手圏の実零頂点である。 -/
theorem stableHomZeroVertex_of_zeroTarget {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (hB : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory B)
    (v : (A ⟶[SSet.{u}] B) _⦋0⦌) : StableHomZeroVertex A B v := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableHomAmbient A B).app (Opposite.op ⦋0⦌) v)
  have h := isZeroVertex_functorVertex_of_pointwise (stableHomExactMap v).hom
    (fun a => hB ((stableHomExactMap v).hom.app (Opposite.op ⦋0⦌) a))
  exact (stableHomAmbient_vertex v).symm ▸ h

/-- 零始域からの元の完全関手は、完全性により関手圏の実零頂点である。 -/
theorem stableHomZeroVertex_of_zeroSource {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory A)
    (v : (A ⟶[SSet.{u}] B) _⦋0⦌) : StableHomZeroVertex A B v := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableHomAmbient A B).app (Opposite.op ⦋0⦌) v)
  have h := isZeroVertex_functorVertex_of_pointwise (stableHomExactMap v).hom
    (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := (stableHomExactMap v).hom) a (hA a))
  exact (stableHomAmbient_vertex v).symm ▸ h

/-- 零標的への元の完全関手の Kan Hom は全境界を充填する。 -/
theorem stableHom_isContractibleKan_of_zeroTarget (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (hB : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (A ⟶[SSet.{u}] B) := by
  intro n b
  exact zeroStableHomBoundary_fill n b (fun v => stableHomZeroVertex_of_zeroTarget hB _)

/-- 零始域からの元の完全関手の Kan Hom も全境界を充填する。 -/
theorem stableHom_isContractibleKan_of_zeroSource (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory A) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (A ⟶[SSet.{u}] B) := by
  intro n b
  exact zeroStableHomBoundary_fill n b (fun v => stableHomZeroVertex_of_zeroSource hA _)

end SerrePositivity.KST.Fibration
