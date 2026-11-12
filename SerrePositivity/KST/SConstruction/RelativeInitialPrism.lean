module
public import SerrePositivity.KST.SConstruction.ZeroNaturalTransformations

/-! # 固定した始対象からの prism の相対延長
概要：始点を一つの始対象に固定した prism を、既存部分と終点を保持して延長する。
方針：区間境界と既存部分の和を貼り、新しい単体の始頂点で充填する。
規約：既存部分の prism は定値とは仮定しない。使われ方：第二の θ の零 subobject の固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定始対象からの既存の prism は始点・終点を保って相対延長できる。
方針：積の和の新しい単体は時刻零から始まるので始対象性で境界を埋める。
規約：標的の quasicategory 性やモデル構造を要求しない。使われ方：固定零始点の矢印の持ち上げ。 -/
lemma exists_relative_initialPrism {B C : SSet.{u}} (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (S : B.Subcomplex) (f : B ⟶ C) (H : (Δ[1] : SSet.{u}) ⊗ (S : SSet.{u}) ⟶ C)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (S : SSet.{u}) ≫ H = SSet.const z)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (S : SSet.{u}) ≫ H = S.ι ≫ f) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ C,
      (Δ[1] ◁ S.ι) ≫ F = H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ F = SSet.const z ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ F = f := by
  let T := boundary.{u} 1
  let q := Subcomplex.unionProd.isPushout T S
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const z : B ⟶ C) f
  have hw : (T.ι ▷ (S : SSet.{u})) ≫ H = ((T : SSet.{u}) ◁ S.ι) ≫ h := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, SSet.comp_const]
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict H
    rw [h₀, h₁] at he
    exact he
  let a := q.desc H h hw
  have ha₁ : Subcomplex.unionProd.ι₁ T S ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ T S ≫ a = h := q.inr_desc _ _ _
  let A := Subcomplex.unionProd T S
  have hvT (x : (Δ[1] : SSet.{u}) _⦋0⦌) : x ∈ T.obj (Opposite.op ⦋0⦌) := by
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 (stdSimplex.obj₀Equiv x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  have hA : ∀ v : ((Δ[1] : SSet.{u}) ⊗ B) _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    exact (Subcomplex.mem_unionProd_iff T S v).2 (Or.inr (hvT v.1))
  have eval_a (v : ((Δ[1] : SSet.{u}) ⊗ B) _⦋0⦌) :
      a.app (Opposite.op ⦋0⦌) ⟨v, hA v⟩ =
        h.app (Opposite.op ⦋0⦌) (⟨v.1, hvT v.1⟩, v.2) := by
    let w : ((T : SSet.{u}) ⊗ B) _⦋0⦌ := (⟨v.1, hvT v.1⟩, v.2)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ha₂ (Opposite.op ⦋0⦌)) w
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_of_initial_or_terminal_endpoints A hA a (by
    intro n s hs
    have hi : s.1 ∉ (horn 1 1).obj (Opposite.op ⦋n + 1⦌) := by
      intro hi
      obtain ⟨k, _hk, hr⟩ := (mem_horn_iff_notMem_range s.1 1).1 hi
      exact hs ((Subcomplex.mem_unionProd_iff T S s).2
        (Or.inr ((mem_boundary_iff_notMem_range s.1).2 ⟨k, hr⟩)))
    left
    rw [eval_a]
    have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_interval_firstVertex_of_notMem_lastHorn s.1 hi
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (if (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1 : (Δ[1] : SSet.{u}) _⦋0⦌) 0 = 0
      then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 0 else f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.2))
    rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact hz)
  have hb : (T.ι ▷ B) ≫ F = h := by
    rw [← Subcomplex.unionProd.ι₂_ι T S, Category.assoc, hF, ha₂]
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι T S, Category.assoc, hF, ha₁]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0 B, Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1 B, Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

end SerrePositivity.KST.SConstruction
