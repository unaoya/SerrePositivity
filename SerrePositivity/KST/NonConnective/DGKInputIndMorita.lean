module
public import SerrePositivity.KST.NonConnective.DGKInputIndEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMorita
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：元の厳密 dg Morita 射の全族から回収した Indω 作用は実同値。
方針：同じ固定 ν 射の Morita 同値を宇宙移送し、元の Yoneda 制限同値で延長する。
規約：元の全族の指定頂点を保持する。懸垂の全入力作用や非連結 K の不変性は別工程。
使われ方：K-7 d4・e の固定 ν と Ind 作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 同じ全 native 族の dg 頂点は、元の固定 ν 射の指定 Ind 延長そのもの。 -/
theorem dgKInputIndNativeMap_eq_extension (f : A ⟶ B) :
    dgKInputIndNativeMap R A B f = dgKInputIndExtension R A B
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgKInputNuMap R f).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((dgKInputIndRestrictionEquivalence R A B).inv.app (Opposite.op ⦋0⦌)
      (((ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj)).app
        (Opposite.op ⦋0⦌) ((dgKInputCompactNativeLiftedFamilyMap R A B).app
          (Opposite.op ⦋0⦌) (ULift.up (perfDGInputVertexEquiv R A B f))))).val = _
  rw [dgKInputCompactNativeLiftedFamilyMap_vertex]
  rfl

/-- 同じ元の厳密 dg Morita 射の固定 ν 作用は実同値。 -/
theorem dgKInputNuMap_morita_isQCatEquivalence (f : A ⟶ B)
    [(quasiEquivalencePerfectExtension R A B f.down).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKInputNuMap R f).hom := by
  rw [dgKInputNuMap_eq]
  exact (presentedPerfectDGBFMoritaStableEquivalence R f).toQCatEquivalence.isQCatEquivalence

/-- 元の全 native 族の同じ Morita 頂点の実 Indω 作用は同値。 -/
theorem dgKInputIndNativeMap_morita_isQCatEquivalence (f : A ⟶ B)
    [(quasiEquivalencePerfectExtension R A B f.down).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKInputIndNativeMap R A B f) := by
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{max (u + 1) v, max (u + 1) v + 1}
    (dgKInputNuMap_morita_isQCatEquivalence R A B f)
  rw [dgKInputIndNativeMap_eq_extension]
  exact (dgKInputIndEquivalence R A B h.choose).isQCatEquivalence

end SerrePositivity.KST.NonConnective
