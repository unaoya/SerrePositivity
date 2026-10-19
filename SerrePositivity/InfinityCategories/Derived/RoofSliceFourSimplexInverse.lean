module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceFourHorn

/-! # 四次外ホーンの充填から指定四面を保つ実 over 三単体を回収する

概要：回収した四次ホーンの実充填は、元の over 境界の四面を厳密に延長する。
方針：点との join へ戻し、四面体回収の単射性で全四面を照合する。
規約：実充填の存在は入力。使われ方：高次残差方程式の充填を実整合性へ戻す。
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

/-- 実 over 二単体の回収四面体は、最後の頂点を指定点へ固定する。 -/
lemma roofPointSliceTetrahedron_fixed (σ : (sliceOver a) _⦋2⦌) :
    SSet.stdSimplex.map (PinchedHom.lastVertex 2) ≫ roofPointSliceTetrahedron a σ = a := by
  rw [← joinStdSimplexIso_rightPoint_inr]
  change (joinInr Δ[2] Δ[0] ≫ (joinStdSimplexIso 2 0).hom) ≫
    ((joinStdSimplexIso 2 0).inv ≫ σ.val) = a
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact σ.property

/-- 指定零面を持つ四単体を、終点を固定した実 over 三単体へ戻す。 -/
def roofPointSliceThreeSimplexOfFourSimplex (σ : (sliceOver a) _⦋2⦌) (F : Δ[4] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin 5) ≫ F = roofPointSliceTetrahedron a σ) :
    (sliceOver a) _⦋3⦌ :=
  ⟨(joinStdSimplexIso 3 0).hom ≫ F, by
    rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr]
    have he : SSet.stdSimplex.map (PinchedHom.lastVertex 3) =
        SSet.stdSimplex.map (PinchedHom.lastVertex 2) ≫ SSet.stdSimplex.δ (0 : Fin 5) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    rw [he, Category.assoc, h₀]
    exact roofPointSliceTetrahedron_fixed a σ⟩

/-- 回収した実 over 三単体の四面は、元の四単体の最初の四面。 -/
lemma roofPointSliceThreeSimplexOfFourSimplex_face (σ : (sliceOver a) _⦋2⦌)
    (F : Δ[4] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin 5) ≫ F = roofPointSliceTetrahedron a σ) (i : Fin 4) :
    roofPointSliceTetrahedron a ((sliceOver a).δ i
      (roofPointSliceThreeSimplexOfFourSimplex a σ F h₀)) = SSet.stdSimplex.δ i.castSucc ≫ F := by
  have he : PinchedHom.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
    fin_cases i <;> decide
  have hi : joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ (joinStdSimplexIso 3 0).hom =
      (joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.δ i.castSucc :=
    (joinStdSimplexIso_rightPoint_naturality (SimplexCategory.δ i)).trans
      (congrArg (fun f => (joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.map f) he)
  change (joinStdSimplexIso 2 0).inv ≫
    (joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ ((joinStdSimplexIso 3 0).hom ≫ F)) = _
  rw [← Category.assoc (joinMap _ _) _ F, hi, Category.assoc, Iso.inv_hom_id_assoc]

variable (B : ThreeSimplexFaceBoundary (sliceOver a)) (F : Δ[4] ⟶ X)

/-- 指定四次ホーンの実充填から得る、元の over 三次境界の実充填。 -/
def roofPointSliceFourHornOverFiller
    (hF : (horn 4 4).ι ≫ F = roofPointSliceFourHorn a B) : (sliceOver a) _⦋3⦌ :=
  roofPointSliceThreeSimplexOfFourSimplex a (B.face 0) F
    (by rw [← horn.ι_ι_assoc (4 : Fin 5) 0 (by decide), hF]
        exact roofPointSliceFourHorn_face a B 0)

/-- 回収した実 over 三単体は、元の指定四面を全て厳密に保つ。 -/
lemma roofPointSliceFourHornOverFiller_face
    (hF : (horn 4 4).ι ≫ F = roofPointSliceFourHorn a B) (i : Fin 4) :
    (sliceOver a).δ i (roofPointSliceFourHornOverFiller a B F hF) = B.face i := by
  apply roofPointSliceTetrahedron_injective a
  dsimp only [roofPointSliceFourHornOverFiller]
  rw [roofPointSliceThreeSimplexOfFourSimplex_face]
  rw [← horn.ι_ι_assoc (4 : Fin 5) i.castSucc (Fin.castSucc_ne_last i), hF]
  exact roofPointSliceFourHorn_face a B i

end SerrePositivity.InfinityCategories
