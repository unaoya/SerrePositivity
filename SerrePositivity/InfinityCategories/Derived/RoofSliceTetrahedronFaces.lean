module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTetrahedronInverse

/-! # 実 over 二単体が指定する四面体と三面の回収

概要：点上の over 二単体を元の単体集合の三単体へ移し、最初の三面を照合する。
方針：点との join の標準単体同型の自然性を用いる。
規約：終点は元の点に固定される。使われ方：実二単体の整合性を四次ホーンへ移す。
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

/-- 実 over 二単体が指定する、元の単体集合の四面体。 -/
def roofPointSliceTetrahedron (σ : (sliceOver a) _⦋2⦌) : Δ[3] ⟶ X :=
  (joinStdSimplexIso 2 0).inv ≫ σ.val

/-- 回収した四面体の最初の三面は、元の実 over 二単体の三辺の回収三角形。 -/
lemma roofPointSliceTetrahedron_face (σ : (sliceOver a) _⦋2⦌) (i : Fin 3) :
    SSet.stdSimplex.δ i.castSucc ≫ roofPointSliceTetrahedron a σ =
      roofPointSliceTriangle a ((sliceOver a).δ i σ) := by
  have he : PinchedHom.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
    fin_cases i <;> decide
  have hi : joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ (joinStdSimplexIso 2 0).hom =
      (joinStdSimplexIso 1 0).hom ≫ SSet.stdSimplex.δ i.castSucc :=
    (joinStdSimplexIso_rightPoint_naturality (SimplexCategory.δ i)).trans
      (congrArg (fun f => (joinStdSimplexIso 1 0).hom ≫ SSet.stdSimplex.map f) he)
  have h : SSet.stdSimplex.δ i.castSucc ≫ (joinStdSimplexIso 2 0).inv =
      (joinStdSimplexIso 1 0).inv ≫ joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) := by
    apply (cancel_epi (joinStdSimplexIso 1 0).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change SSet.stdSimplex.δ i.castSucc ≫ ((joinStdSimplexIso 2 0).inv ≫ σ.val) =
    (joinStdSimplexIso 1 0).inv ≫
      (joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ σ.val)
  rw [← Category.assoc, h, Category.assoc]

/-- 四面体の回収は実 over 二単体を区別する。 -/
lemma roofPointSliceTetrahedron_injective {σ τ : (sliceOver a) _⦋2⦌}
    (h : roofPointSliceTetrahedron a σ = roofPointSliceTetrahedron a τ) : σ = τ := by
  apply Subtype.ext
  exact (cancel_epi (joinStdSimplexIso 2 0).inv).mp h

end SerrePositivity.InfinityCategories
