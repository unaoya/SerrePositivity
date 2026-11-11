module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor

/-!
概要：全係数を持つ標準単体を、同じ係数付き前面へ終点を追加した join へ移す。
方針：元の標準 join 同型と直積の比較を使う。
規約：元の全面を厳密に保持。使われ方：実四面体の 012 面の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全係数付き単体を、同じ前面と追加終点の join へ移す。 -/
def simplexConeParameter (n : ℕ) (P : SSet.{u}) :
    (Δ[n + 1] : SSet.{u}) ⊗ P ⟶ join (Δ[n] ⊗ P) Δ[0] :=
  (β_ Δ[n + 1] P).hom ≫ (P ◁ (joinStdSimplexIso n 0).inv) ≫
    joinTensorLeft P Δ[n] Δ[0] ≫ joinMap (β_ P Δ[n]).hom (𝟙 Δ[0])

/-- 元の最終点を除いた前面は、同じ全係数付き単体の左包含として回収される。 -/
lemma simplexConeParameter_front (n : ℕ) (P : SSet.{u}) :
    (stdSimplex.map (PinchedHom.front n) ▷ P) ≫ simplexConeParameter n P =
      joinInl (Δ[n] ⊗ P) Δ[0] := by
  have hs : (stdSimplex.map (PinchedHom.front n) ▷ P) ≫ (β_ Δ[n + 1] P).hom =
      (β_ Δ[n] P).hom ≫ (P ◁ stdSimplex.map (PinchedHom.front n)) := by
    apply SSet.hom_ext
    intro d
    rfl
  have hi : stdSimplex.map (PinchedHom.front n) ≫ (joinStdSimplexIso n 0).inv =
      joinInl (Δ[n] : SSet.{u}) Δ[0] := by
    rw [← joinStdSimplexIso_rightPoint_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [simplexConeParameter, ← Category.assoc, hs, Category.assoc,
    ← whiskerLeft_comp_assoc, hi]
  have hj : (P ◁ joinInl (Δ[n] : SSet.{u}) Δ[0]) ≫ joinTensorLeft P Δ[n] Δ[0] ≫
      joinMap (β_ P Δ[n]).hom (𝟙 Δ[0]) =
    (β_ P Δ[n]).hom ≫ joinInl (Δ[n] ⊗ P) Δ[0] := by
    rw [← Category.assoc, joinTensorLeft_inl, joinInl_joinMap]
  rw [hj]
  apply SSet.hom_ext
  intro d
  rfl

end SerrePositivity.InfinityCategories.F2
