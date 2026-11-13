module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Fintype.EquivFin

/-!
概要：アフィン開集合の開被覆に、有限の標準開細分を作る。
方針：各点で標準開を選び、その切断が単位イデアルを生成することから有限個を取る。
規約：有限被覆の添字は Fin n とし、座標環の宇宙による添字の制限を残さない。
使われ方：任意のアフィン被覆の Čech 完全性を標準開の計算に帰着する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u v
variable {X : Scheme.{u}} {κ : Type v} (U : X.Opens) (hU : IsAffineOpen U)
variable (V : κ → X.Opens)

include hU in
/-- アフィン開集合の任意の開被覆は、単位イデアルを生成する有限標準開被覆で細分できる。 -/
theorem schemeFinitePrincipalRefinement (hcover : (⨆ i, V i) = U) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)) (ρ : Fin n → κ),
      Ideal.span (Set.range f) = ⊤ ∧ ∀ j, X.basicOpen (f j) ≤ V (ρ j) := by
  classical
  have hp : ∀ x : U, ∃ (i : κ) (g : Γ(X, U)),
      X.basicOpen g ≤ V i ∧ x.val ∈ X.basicOpen g := by
    intro x
    have hx : x.val ∈ ⨆ i, V i := by rw [hcover]; exact x.property
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le ⟨x.val, hi⟩ x.property
    exact ⟨i, g, hg, hxg⟩
  choose i g hg hxg using hp
  have hs : Ideal.span (Set.range g) = ⊤ := by
    apply (hU.self_le_iSup_basicOpen_iff (s := Set.range g)).mp
    intro x hx
    apply Opens.mem_iSup.mpr
    exact ⟨⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, hxg ⟨x, hx⟩⟩
  obtain ⟨S, hS, hs⟩ := (Ideal.span_eq_top_iff_finite (Set.range g)).mp hs
  choose y hy using (fun a : S ↦ hS a.property)
  let e := S.equivFin
  let f : Fin S.card → Γ(X, U) := fun j ↦ (e.symm j).val
  refine ⟨S.card, f, (fun j ↦ i (y (e.symm j))), ?_, ?_⟩
  · have hr : Set.range f = (S : Set Γ(X, U)) := by
      ext a
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).property
      · intro ha
        refine ⟨e ⟨a, ha⟩, ?_⟩
        simp [f]
    rw [hr]
    exact hs
  · intro j
    change X.basicOpen (e.symm j).val ≤ V (i (y (e.symm j)))
    rw [← hy (e.symm j)]
    exact hg (y (e.symm j))

end SerrePositivity.AlgebraicGeometry
