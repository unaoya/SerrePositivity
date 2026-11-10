module

public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.PrismBoundaryExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：可逆な辺の path の始点評価の持ち上げ性。
方針：境界上の path を可逆な垂直辺を持つ prism として延長する。
規約：標的は quasicategory、評価する端点は零。
使われ方：Kerodon Corollary 4.5.3.24、Theorem 4.8.4.1 の還元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆 path の始点評価は trivial Kan fibration。
方針：正次元では境界上の prism と始点の単体を延長し、全部分複体へ戻す。
規約：標的の quasicategory 性だけを仮定する。
使われ方：Kerodon Corollary 4.5.3.24 の始点側の評価。 -/
@[kerodon 02BY]
instance trivialKanFibration_equivalencePathEndpoint_zero (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration (equivalencePathEndpoint Y 0) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    refine CommSq.HasLift.mk' { l := b ≫ equivalencePathRefl Y, fac_left := ?_, fac_right := ?_ }
    · apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro x
      have hx : x.val ∈ (boundary 0).obj (Opposite.op ⦋d⦌) := x.property
      generalize x.val = z at hx
      rw [boundary_zero] at hx
      exact False.elim hx
    · rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  | succ n =>
    let H := uncurry (a ≫ equivalencePathι Y)
    have hC : curry H = a ≫ equivalencePathι Y := curry_uncurry _
    have h₀ : (boundary (n + 1)).ι ≫ b =
        prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← curry_evaluateFunctorAt_interval, hC]
      exact sq.w.symm
    have hH : IsInvertibleEdge (edgeOfSimplex
        (H.app (Opposite.op ⦋1⦌) (prismBoundaryFirstVerticalEdge n))) := by
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨stdSimplex.obj₀Equiv.symm 0, vertex_mem_boundary n 0⟩
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      change IsEquivalencePathVertex ((a ≫ equivalencePathι Y).app (Opposite.op ⦋0⦌) x) at hx
      rw [← hC] at hx
      unfold IsEquivalencePathVertex at hx
      rw [intervalFunctorVertexEdge_curry] at hx
      exact hx
    obtain ⟨F, hF, hF₀⟩ := prism_extend_boundary_with_endpoint n H b h₀ hH
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ equivalencePathι Y := by
      rw [← curry_natural_left, hF, hC]
    have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
        IsEquivalencePathVertex ((curry F).app (Opposite.op ⦋0⦌) v) := by
      intro v
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨v, by
          have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
          rw [Equiv.symm_apply_apply] at h
          exact h⟩
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) x
      change (curry F).app (Opposite.op ⦋0⦌) v =
        (a.app (Opposite.op ⦋0⦌) x).val at he
      exact he.symm ▸ hx
    let g := fullSubcomplexLift IsEquivalencePathVertex (curry F) hv
    have hg : g ≫ equivalencePathι Y = curry F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · have : Mono (equivalencePathι Y) := by unfold equivalencePathι; infer_instance
      apply (cancel_mono (equivalencePathι Y)).1
      rw [Category.assoc, hg, hc]
    · change g ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = b
      rw [← Category.assoc, hg, curry_evaluateFunctorAt_interval, hF₀]

/-- 概要：可逆 path の単体集合は quasicategory。
方針：始点評価が inner fibration であることを使う。
規約：標的の quasicategory 性を仮定する。
使われ方：Kerodon §4.5.3 の関手の同値の空間。 -/
instance equivalencePath_quasicategory (Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (equivalencePath Y) :=
  quasicategory_of_innerFibration (equivalencePathEndpoint Y 0)

/-- 概要：単射上の可逆な垂直辺を持つホモトピーは始点の延長と共に延長できる。
方針：可逆 path の始点評価の単射に対する持ち上げを uncurry する。
規約：始点と単射上の制限は厳密に固定する。
使われ方：Kerodon Corollary 4.5.3.24 の一般の単射に対する形。 -/
lemma equivalenceHomotopy_extend {A B Y : SSet.{u}} [Quasicategory Y]
    (i : A ⟶ B) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (f : B ⟶ Y)
    (h₀ : prismEndpoint 0 A ≫ H = i ≫ f)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 0 B ≫ F = f ∧
      ∀ x : B _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
        (F.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
  have hv : ∀ x, IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) x) := by
    intro x
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hH x
  let a := fullSubcomplexLift IsEquivalencePathVertex (curry H) hv
  have ha : a ≫ equivalencePathι Y = curry H := fullSubcomplexLift_ι _ _ _
  have hw : a ≫ equivalencePathEndpoint Y 0 = i ≫ f := by
    change a ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = _
    rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval, h₀]
  have := TrivialKanFibration.mem (p := equivalencePathEndpoint Y 0) i inferInstance
  let sq : CommSq a i (equivalencePathEndpoint Y 0) f := ⟨hw⟩
  let F := uncurry (sq.lift ≫ equivalencePathι Y)
  have hC : curry F = sq.lift ≫ equivalencePathι Y := curry_uncurry _
  refine ⟨F, ?_, ?_, ?_⟩
  · apply curry_injective
    rw [curry_natural_left, hC, ← Category.assoc, sq.fac_left, ha]
  · rw [← curry_evaluateFunctorAt_interval, hC]
    exact sq.fac_right
  · intro x
    have hx := fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) x)
    change IsEquivalencePathVertex
      ((sq.lift ≫ equivalencePathι Y).app (Opposite.op ⦋0⦌) x) at hx
    rw [← hC] at hx
    unfold IsEquivalencePathVertex at hx
    rw [intervalFunctorVertexEdge_curry] at hx
    exact hx

end SerrePositivity.InfinityCategories
