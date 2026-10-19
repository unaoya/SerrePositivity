module
public import SerrePositivity.KST.SConstruction.DiagonalAssembly

/-! # 区間族の両端の零化と全境界の零化
概要：通常の cylinder の両端が同じ基点に写れば、区間の全境界が厳密に基点へ写る。
方針：境界の各単体の定値性と零・一次の端点の式を使う。
規約：源・標的の Kan 性は不要。使われ方：元の零行収縮の境界像を円から降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 両端が厳密に基点へ写る区間族は、区間の全境界上で基点に定数。 -/
lemma cylinder_boundary_constant {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₀ : SSet.ι₀ ≫ h = toUnit A ≫ B.hom)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) :
    (A ◁ (boundary 1).ι) ≫ h = toUnit (A ⊗ (boundary 1 : (Δ[1] : SSet.{u}).Subcomplex)) ≫
      B.hom := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  let t : (Δ[1] : SSet.{u}) _⦋d.unop.len⦌ := z.2.val
  have hc := intervalBoundary_simplex_constant t z.2.property
  have hz (i : Fin 2) : (if i = 0 then True else i = 1) := by fin_cases i <;> decide
  have hi : t 0 = 0 ∨ t 0 = 1 := by
    have hi := hz (t 0)
    split_ifs at hi with hi0
    · exact Or.inl hi0
    · exact Or.inr hi
  rcases hi with hi | hi
  · have ht : t = ((SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})).app d z.1).2 := by
      apply stdSimplex.objEquiv.injective
      rw [hc, hi]
      rfl
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app h₀ d) z.1
    change h.app d (z.1, t) = _
    rw [ht]
    exact he
  · have ht : t = ((SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})).app d z.1).2 := by
      apply stdSimplex.objEquiv.injective
      rw [hc, hi]
      rfl
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app h₁ d) z.1
    change h.app d (z.1, t) = _
    rw [ht]
    exact he

end SerrePositivity.KST.SConstruction
