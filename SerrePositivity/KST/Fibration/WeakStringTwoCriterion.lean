module
public import SerrePositivity.KST.Fibration.WeakStringsStability
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreFaces

/-! # 二辺の W 列の元の短辺による判定

実二単体の合成関係を使い、二つの短辺の W 条件だけから全合成辺の条件を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 実二単体が core に入ることは、その二つの短辺が可逆であることと同値。 -/
lemma coreTriangle_iff_shortEdges {X : SSet.{u}} (s : X _⦋2⦌) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).obj (Opposite.op ⦋2⦌) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 2 s)) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 0 s)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_triangle_iff]
  constructor
  · intro h
    exact ⟨h 2, h 0⟩
  · rintro ⟨h₂, h₀⟩ i
    have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_triangle_missing s 1 (fun j hj => by
      fin_cases j
      · exact h₀
      · exact (hj rfl).elim
      · exact h₂)
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂

/-- W 列の二単体の頂点条件は、元の二つの短辺への制限の W 条件と同値。 -/
lemma weakStringTwoPredicate_iff_shortEdges {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[2] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakStringPredicate q ⦋2⦌ v ↔
      weakArrowPredicate q (((pre (stdSimplex.δ (2 : Fin 3))).app B.obj).app (Opposite.op ⦋0⦌) v) ∧
      weakArrowPredicate q
        (((pre (stdSimplex.δ (0 : Fin 3))).app B.obj).app (Opposite.op ⦋0⦌) v) := by
  have he (α : ⦋1⦌ ⟶ ⦋2⦌) : weakArrowPredicate q
      (((pre (stdSimplex.map α)).app B.obj).app (Opposite.op ⦋0⦌) v) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (C.obj.map α.op
        (q.hom.app (Opposite.op ⦋2⦌) (simplexVertexValue ⦋2⦌ v)))) := by
    rw [← weakStringPredicate_one_iff]
    unfold weakStringPredicate
    rw [simplexVertexValue_reindex, NatTrans.naturality_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff]
  exact (coreTriangle_iff_shortEdges _).trans (and_congr
    (he (SimplexCategory.δ (2 : Fin 3))).symm (he (SimplexCategory.δ (0 : Fin 3))).symm)

end SerrePositivity.KST.Fibration
