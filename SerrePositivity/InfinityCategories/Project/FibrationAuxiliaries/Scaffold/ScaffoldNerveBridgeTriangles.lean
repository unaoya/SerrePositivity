module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldNerveBridgeEdgeImages

/-!
概要：最初の辺と尾部から欠ける辺を、同じ底の三角形で二辺へ分解する。
方針：欠損辺は零から正の頂点へ向かうので、頂点一を経由する。
規約：元の長辺を厳密に保持し、短辺は同じ pushout 比較の像に取る。
使われ方：高次単体で元の cocartesian 辺保存を反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold

/-- 同じ比較に欠ける各辺は、像に含まれる二辺の三角形の同じ長辺になる。 -/
lemma scaffoldFiniteNerveBridge_missing_edge_triangle (n : ℕ)
    (b : (nerve (ULift.{u} (Fin (n + 2)))) _⦋1⦌)
    (hb : b ∉ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n).app (Opposite.op ⦋1⦌))) :
    ∃ s : (Δ[2] : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 2))),
      stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm b ∧
      SSet.yonedaEquiv (stdSimplex.δ 2 ≫ s) ∈
        Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n).app (Opposite.op ⦋1⦌)) ∧
      SSet.yonedaEquiv (stdSimplex.δ 0 ≫ s) ∈
        Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n).app (Opposite.op ⦋1⦌)) := by
  have h0 : b.obj 0 = ULift.up (0 : Fin (n + 2)) := by
    apply ULift.ext
    by_contra h
    exact hb (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveBridge_tail_edge_mem n b h)
  have h1 : (b.obj 1).down ≠ 0 := by
    intro hz
    let z : ComposableArrows (ULift.{u} (Fin 2)) 1 :=
      (CategoryTheory.Functor.const _).obj (ULift.up 0)
    have he : (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)).app (Opposite.op ⦋1⦌) z = b := by
      refine CategoryTheory.Functor.ext (fun i ↦ ?_)
        (fun _ _ _ ↦ Subsingleton.elim _ _)
      apply ULift.ext
      apply Fin.ext
      have hi := leOfHom (b.map (homOfLE (Fin.le_last i)))
      change (b.obj i).down.val ≤ (b.obj 1).down.val at hi
      have hz' := congrArg Fin.val hz
      change (b.obj 1).down.val = 0 at hz'
      change 0 = (b.obj i).down.val
      omega
    apply hb
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveBridge_first_edge_mem n z
  let f : b.obj 0 ⟶ ULift.up (1 : Fin (n + 2)) := homOfLE (by
    rw [h0]
    change (0 : ℕ) ≤ 1
    omega)
  let g : ULift.up (1 : Fin (n + 2)) ⟶ b.obj 1 := homOfLE (by
    change 1 ≤ (b.obj 1).down.val
    have hz : (b.obj 1).down.val ≠ 0 := fun h ↦ h1 (Fin.ext h)
    omega)
  refine ⟨SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f g), ?_, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, nerve.δ₁_mk₂_eq]
    congr 1
    refine CategoryTheory.Functor.ext (fun i ↦ ?_)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
    fin_cases i <;> rfl
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, nerve.δ₂_mk₂_eq]
    let e : ComposableArrows (ULift.{u} (Fin 2)) 1 :=
      ComposableArrows.mk₁ (homOfLE (show (ULift.up (0 : Fin 2) : ULift.{u} _) ≤
        ULift.up 1 by decide))
    have he : ComposableArrows.mk₁ f =
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)).app (Opposite.op ⦋1⦌) e := by
      refine CategoryTheory.Functor.ext (fun i ↦ ?_)
        (fun _ _ _ ↦ Subsingleton.elim _ _)
      fin_cases i
      · exact h0
      · rfl
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveBridge_first_edge_mem n e
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, nerve.δ₀_mk₂_eq]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveBridge_tail_edge_mem n _ (by
      intro h
      have hv := congrArg Fin.val h
      change (1 : ℕ) = 0 at hv
      omega)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
