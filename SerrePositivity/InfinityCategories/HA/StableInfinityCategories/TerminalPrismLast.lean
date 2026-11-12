module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalPrismBoundary

/-! # 最後の終点だけを仮定した prism の境界延長

概要：区間の始点側とパラメーターの境界上の図式は、最後の終点が終対象なら延長できる。
方針：新しい単体は両因子の指定部分の外にあるので、最後の頂点が両座標の終端となる。
規約：他の境界頂点の終対象性は仮定しない。
使われ方：S4 の span 比較の一意性を支える相対終点境界充填。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：prism の始点側と境界の図式は、最後の終点が終対象なら延長できる。
方針：和の部分複体の外のセルの最後の頂点が、指定した一頂点になることを使う。
規約：quasicategory 性は不要。使われ方：終対象へ向かう辺の相対境界充填。 -/
lemma stable_prism_extend_terminal_last {X : SSet.{u}} (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ X)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ X,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ F = F₀ := by
  let S := horn.{u} 1 0
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := q.desc H (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := q.inr_desc _ _ _
  let A := Subcomplex.unionProd S T
  have hA : ∀ v : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    apply Or.inl
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hterm : ∀ (m : ℕ) (s : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    intro m s hs
    have hs₁ : s.1 ∉ S.obj (Opposite.op ⦋m + 1⦌) := fun h ↦ hs (Or.inr ⟨h, by trivial⟩)
    have hs₂ : s.2 ∉ T.obj (Opposite.op ⦋m + 1⦌) := fun h ↦ hs (Or.inl ⟨by trivial, h⟩)
    have hv₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have hv₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_interval_lastVertex_of_notMem_firstHorn s.1 hs₁
    let v : (T : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2, by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2))
      rw [Equiv.symm_apply_apply] at h
      exact h⟩
    let w : ((Δ[1] : SSet.{u}) ⊗ (T : SSet.{u})) _⦋0⦌ :=
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v)
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋0⦌)) w
    have he : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩ =
        H.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v) := by
      change a.app (Opposite.op ⦋0⦌)
        ⟨(stdSimplex.obj₀Equiv.symm (1 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2), _⟩ =
          H.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v) at hh
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_prod, hv₁]
      exact hh
    rw [he]
    have hv : v = ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ :=
      Subtype.ext hv₂
    rw [hv]
    exact ht
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_of_terminal_last_vertices A hA a hterm
  refine ⟨F, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h : (S.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F =
        snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
    have h' := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection (Δ[n + 1] : SSet.{u}) ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
