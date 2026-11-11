module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：cocartesian な最初の辺を持つ合成三角形を、指定した底の三角形上へ持ち上げる。
方針：二次の零番目ホーンを二つの辺の pushout で作り、最初の辺の相対充填を使う。
規約：底の三角形と二つの指定辺を厳密に固定する。left fibration 性は要求しない。
使われ方：一般の cocartesian fibration の終点指定の可逆辺持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- cocartesian な最初の辺と指定した長辺を持つ三角形は、同じ底の三角形上に持ち上がる。 -/
lemma cocartesianEdge_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y)
    {x₀ x₁ x₂ : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₁)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q f.edge)
    (h : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₂)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₁) (q.app (Opposite.op ⦋0⦌) x₂))
    (t : SSet.Truncated.Edge.CompStruct (f.map ((truncation 2).map q)) g
      (h.map ((truncation 2).map q))) :
    Nonempty (Σ g' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂,
      {t' : SSet.Truncated.Edge.CompStruct f g' h //
        q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex}) := by
  obtain ⟨a, ha₁, ha₂⟩ := horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm h.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (f.src_eq.trans h.src_eq.symm))
  have sq : CommSq a (horn 2 0).ι q (SSet.yonedaEquiv.symm t.simplex) := by
    constructor
    apply horn₂₀.isPushout.hom_ext
    · simp only [← Category.assoc, ha₁, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₂.symm
    · simp only [← Category.assoc, ha₂, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₁.symm
  have hai : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0) = f.edge := by
    have ht := congrArg SSet.yonedaEquiv ha₁
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at ht
    have hi : SSet.yonedaEquiv horn₂₀.ι₀₁ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0 := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rwa [hi] at ht
  have := hf 0 a (SSet.yonedaEquiv.symm t.simplex) hai sq
  let F := sq.lift
  have hF₂ : stdSimplex.δ 2 ≫ F = SSet.yonedaEquiv.symm f.edge := by
    rw [← horn.ι_ι_assoc 0 2 (by decide), sq.fac_left, ha₁]
    rfl
  have hF₁ : stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm h.edge := by
    rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left, ha₂]
    rfl
  let s := SSet.yonedaEquiv F
  have h₂ : X.δ 2 s = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₂]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have h₁ : X.δ 1 s = h.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁]
    exact SSet.yonedaEquiv.apply_symm_apply h.edge
  have hsrc : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) = x₁ := by
    have he : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) =
        X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₂]
    exact f.tgt_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) s) = x₂ := by
    have he : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) s) =
        X.δ (0 : Fin 2) (X.δ (1 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₁]
    exact h.tgt_eq
  let g' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂ :=
    ⟨X.δ 0 s, hsrc, htgt⟩
  refine ⟨g', ⟨⟨s, h₂, rfl, h₁⟩, ?_⟩⟩
  change q.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv sq.lift) = _
  rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
