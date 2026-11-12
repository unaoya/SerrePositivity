module
public import SerrePositivity.KST.Fibration.SComponentExactness

/-! # 元の相対 S_n 辺を、同じ実 cofiber 図式の全成分で判定する

各成分ごとの別々の cofiber の選択には置き換えず、元の一つの cofiber 正方形を評価する。
S_n 商の局所化普遍性はここでは主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
  {x y : (sConstruction n B.obj) _⦋0⦌}
  {f : Truncated.Edge (X := (truncation 2).obj (sConstruction n B.obj)) x y}
include h

/-- 元の相対辺の条件は、同じ cofiber 図式の全 Ar 成分が元の核像に属すること。 -/
theorem relativeSConstruction_mem_edge_iff_cofiber_components (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    f.edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      ∀ a : (arNerve n) _⦋0⦌,
        (sComponentEvaluation B.obj n a).app (Opposite.op ⦋0⦌) s.cofiber ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i := by
  rw [relativeSConstruction_mem_edge_iff h]
  exact forall_congr' (fun a => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff h
    (s.map (sComponentEvaluation B.obj n a)))

/-- 同じ S 後合成で写した元の cofiber が零であることが、元の相対辺条件と同値。 -/
theorem relativeSConstruction_mem_edge_iff_cofiber_zero (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    f.edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcomp n q.hom (exactMap_preservesSData q)).app
        (Opposite.op ⦋0⦌) s.cofiber) := by
  rw [relativeSConstruction_mem_edge_iff_cofiber_components h n s,
    sConstruction_isZeroVertex_iff_components]
  apply forall_congr'
  intro a
  have he := congrArg (fun m : sConstruction n B.obj ⟶ C.obj =>
    m.app (Opposite.op ⦋0⦌) s.cofiber)
    (sPostcomp_gapped_evaluate n q.hom (exactMap_preservesSData q) a)
  exact (h.kernel _).symm.trans (iff_of_eq
    (congrArg (fun z : C.obj _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) he.symm))

/-- 元の相対 S_n 辺は、元の同じ S 後合成で反転される辺に正確に一致する。 -/
theorem relativeSConstruction_mem_edge_iff_sPostcomp_invertible
    (f : Truncated.Edge (X := (truncation 2).obj (sConstruction n B.obj)) x y) :
    f.edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := sConstruction n C.obj) (f.map ((truncation 2).map
        (sPostcomp n q.hom (exactMap_preservesSData q)))) := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  exact (relativeSConstruction_mem_edge_iff_cofiber_zero h n s).trans
    (s.map_isInvertible_iff_zero (sPostcomp n q.hom (exactMap_preservesSData q))).symm

end SerrePositivity.KST.Fibration
