module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTetrahedronFaces

/-! # 実 over 辺の終点退化と回収四面体

概要：over 辺の終点を繰り返す標準二単体の回収四面体は、元の三角形の正番号退化。
方針：点との join 同型の自然性と extend の退化番号を照合する。
規約：任意の単体集合で成立。使われ方：恒等図式辺の標準錐の閉細分の保存。
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


/-- over 辺の終点を繰り返す退化の回収は、元の三角形の同じ正番号退化。 -/
lemma roofPointSliceTetrahedron_degeneracy_one (σ : (sliceOver a) _⦋1⦌) :
    roofPointSliceTetrahedron a ((sliceOver a).σ 1 σ) =
      SSet.stdSimplex.σ (1 : Fin 3) ≫ roofPointSliceTriangle a σ := by
  have he : PinchedHom.extend (SimplexCategory.σ (1 : Fin 2)) =
      SimplexCategory.σ (1 : Fin 3) := by decide
  have hi : joinMap (SSet.stdSimplex.σ (1 : Fin 2)) (𝟙 Δ[0]) ≫
      (joinStdSimplexIso 1 0).hom =
      (joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.σ (1 : Fin 3) :=
    (joinStdSimplexIso_rightPoint_naturality (SimplexCategory.σ (1 : Fin 2))).trans
      (congrArg (fun f => (joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.map f) he)
  have h : SSet.stdSimplex.σ (1 : Fin 3) ≫ (joinStdSimplexIso 1 0).inv =
      (joinStdSimplexIso 2 0).inv ≫
        joinMap (SSet.stdSimplex.σ (1 : Fin 2)) (𝟙 Δ[0]) := by
    apply (cancel_epi (joinStdSimplexIso 2 0).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (joinStdSimplexIso 2 0).inv ≫
    (joinMap (SSet.stdSimplex.σ (1 : Fin 2)) (𝟙 Δ[0]) ≫ σ.val) =
      SSet.stdSimplex.σ (1 : Fin 3) ≫ ((joinStdSimplexIso 1 0).inv ≫ σ.val)
  rw [← Category.assoc, ← h, Category.assoc]

end SerrePositivity.InfinityCategories
