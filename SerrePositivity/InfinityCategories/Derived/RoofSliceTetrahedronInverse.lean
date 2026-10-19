module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceOuterHorn

/-! # 指定三面を持つ四面体から実 over の二単体を回収する

概要：元の圏で三面が指定図式と二脚に一致する四面体を、実 over の合成三角形へ戻す。
方針：終点を点との join で固定し、全ての面を三つの指定実 over 辺へ照合する。
規約：充填四面体の存在は入力。使われ方：共通始錐の一次整合性の充填判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 実 over の一単体は、回収三角形の最後の頂点を指定点へ固定する。 -/
lemma roofPointSliceTriangle_fixed (σ : (sliceOver a) _⦋1⦌) :
    SSet.stdSimplex.map (PinchedHom.lastVertex 1) ≫ roofPointSliceTriangle a σ = a := by
  rw [← joinStdSimplexIso_rightPoint_inr]
  change (joinInr Δ[1] Δ[0] ≫ (joinStdSimplexIso 1 0).hom) ≫
    ((joinStdSimplexIso 1 0).inv ≫ σ.val) = a
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact σ.property

/-- 回収三角形の厳密等式は、元の実 over の一単体の厳密等式を与える。 -/
lemma roofPointSliceTriangle_injective {σ τ : (sliceOver a) _⦋1⦌}
    (h : roofPointSliceTriangle a σ = roofPointSliceTriangle a τ) : σ = τ := by
  apply Subtype.ext
  exact (cancel_epi (joinStdSimplexIso 1 0).inv).mp h

variable {s₀ s₁ s₂ : (sliceOver a) _⦋0⦌}
variable (e₀₁ : Truncated.Edge (X := (truncation 2).obj (sliceOver a)) s₀ s₁)
variable (e₁₂ : Truncated.Edge (X := (truncation 2).obj (sliceOver a)) s₁ s₂)
variable (e₀₂ : Truncated.Edge (X := (truncation 2).obj (sliceOver a)) s₀ s₂)
variable (F : Δ[3] ⟶ X)
variable (hF₀ : SSet.stdSimplex.δ (0 : Fin 4) ≫ F = roofPointSliceTriangle a e₁₂.edge)

/-- 指定零面を持つ四面体を、終点を固定した実 over の二単体へ移す。 -/
def roofPointSliceTwoSimplexOfTetrahedron : (sliceOver a) _⦋2⦌ :=
  ⟨(joinStdSimplexIso 2 0).hom ≫ F, by
    rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr]
    have he : SSet.stdSimplex.map (PinchedHom.lastVertex 2) =
        SSet.stdSimplex.map (PinchedHom.lastVertex 1) ≫
          SSet.stdSimplex.δ (0 : Fin 4) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    rw [he, Category.assoc, hF₀]
    exact roofPointSliceTriangle_fixed a e₁₂.edge⟩

/-- 四面体から回収する実 over の二単体の全三面は、元の四面体の最初の三面。 -/
lemma roofPointSliceTwoSimplexOfTetrahedron_face (i : Fin 3) :
    roofPointSliceTriangle a ((sliceOver a).δ i
      (roofPointSliceTwoSimplexOfTetrahedron a e₁₂ F hF₀)) =
      SSet.stdSimplex.δ i.castSucc ≫ F := by
  have he : PinchedHom.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
    fin_cases i <;> decide
  have hi : joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ (joinStdSimplexIso 2 0).hom =
      (joinStdSimplexIso 1 0).hom ≫ SSet.stdSimplex.δ i.castSucc :=
    (joinStdSimplexIso_rightPoint_naturality (SimplexCategory.δ i)).trans
      (congrArg (fun f => (joinStdSimplexIso 1 0).hom ≫ SSet.stdSimplex.map f) he)
  change (joinStdSimplexIso 1 0).inv ≫
    (joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ ((joinStdSimplexIso 2 0).hom ≫ F)) = _
  rw [← Category.assoc (joinMap _ _) _ F, hi, Category.assoc, Iso.inv_hom_id_assoc]

/-- 三つの指定実 over 辺を保った合成三角形を、指定三面の四面体から回収する。 -/
def roofPointSliceCompStructOfTetrahedron
    (hF₁ : SSet.stdSimplex.δ (1 : Fin 4) ≫ F = roofPointSliceTriangle a e₀₂.edge)
    (hF₂ : SSet.stdSimplex.δ (2 : Fin 4) ≫ F = roofPointSliceTriangle a e₀₁.edge) :
    Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂ where
  simplex := roofPointSliceTwoSimplexOfTetrahedron a e₁₂ F hF₀
  d₂ := roofPointSliceTriangle_injective a
    ((roofPointSliceTwoSimplexOfTetrahedron_face a e₁₂ F hF₀ 2).trans hF₂)
  d₀ := roofPointSliceTriangle_injective a
    ((roofPointSliceTwoSimplexOfTetrahedron_face a e₁₂ F hF₀ 0).trans hF₀)
  d₁ := roofPointSliceTriangle_injective a
    ((roofPointSliceTwoSimplexOfTetrahedron_face a e₁₂ F hF₀ 1).trans hF₁)

end SerrePositivity.InfinityCategories
