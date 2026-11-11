module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberIsoProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：既存の trivial Kan fibration の二つの持ち上げの比較は、射影後に元の等号へ戻る。
方針：元の比較の fiber 内の同型を同じ射影へ写し、定値写像の像を計算する。
規約：既存の比較同型を選び直さない。
使われ方：大域の元の Hom 自然性と局所の共有頂点三角形の coherence。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元の持ち上げの比較同型を射影すると、指定した同じ可換等式の同型となる。 -/
lemma functorIsoOfTrivialKanFibration_postcomp {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p f g h).postcomp p =
      eqToIso (congrArg (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h) := by
  let q := (ihom A).map p
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v0 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p)
    rw [h]⟩
  let v1 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    rfl⟩
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v0) (hc.isTerminalVertex v1)
  have hh := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIso.map_vertexFiber_projection q b e)
  apply Iso.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g from _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)) p).hom = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans] at hh
  exact hh

/-- 既存の fiber 内比較は、同じ等式の充満忠実な後合成による標準逆像そのもの。 -/
lemma functorIsoOfTrivialKanFibration_eq_preimage {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p f g h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration p).preimageFunctorIso
        (eqToIso (congrArg
          (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration p).postcomp_functorIso_injective
  rw [functorIsoOfTrivialKanFibration_postcomp,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence.IsFullyFaithful.preimageFunctorIso_postcomp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
