module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceFourHorn

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 実 over 二単体の回収四面体は、最後の頂点を指定点へ固定する。 -/
lemma roofPointSliceTetrahedron_fixed (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋2⦌) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a σ = a := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[2] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).hom) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).inv ≫ σ.val) = a
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact σ.property

/-- 指定零面を持つ四単体を、終点を固定した実 over 三単体へ戻す。 -/
def roofPointSliceThreeSimplexOfFourSimplex (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋2⦌) (F : Δ[4] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin 5) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a σ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋3⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 3 0).hom ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
    have he : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 3) =
        SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 2) ≫ SSet.stdSimplex.δ (0 : Fin 5) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    rw [he, Category.assoc, h₀]
    exact roofPointSliceTetrahedron_fixed a σ⟩

/-- 回収した実 over 三単体の四面は、元の四単体の最初の四面。 -/
lemma roofPointSliceThreeSimplexOfFourSimplex_face (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋2⦌)
    (F : Δ[4] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin 5) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a σ) (i : Fin 4) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ i
      (roofPointSliceThreeSimplexOfFourSimplex a σ F h₀)) = SSet.stdSimplex.δ i.castSucc ≫ F := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
    fin_cases i <;> decide
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 3 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.δ i.castSucc :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality (SimplexCategory.δ i)).trans
      (congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).hom ≫ SSet.stdSimplex.map f) he)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 0).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ i) (𝟙 Δ[0]) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 3 0).hom ≫ F)) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) _ F, hi, Category.assoc, Iso.inv_hom_id_assoc]

variable (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ThreeSimplexFaceBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) (F : Δ[4] ⟶ X)

/-- 指定四次ホーンの実充填から得る、元の over 三次境界の実充填。 -/
def roofPointSliceFourHornOverFiller
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn a B) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋3⦌ :=
  roofPointSliceThreeSimplexOfFourSimplex a (B.face 0) F
    (by rw [← horn.ι_ι_assoc (4 : Fin 5) 0 (by decide), hF]
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face a B 0)

/-- 回収した実 over 三単体は、元の指定四面を全て厳密に保つ。 -/
lemma roofPointSliceFourHornOverFiller_face
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn a B) (i : Fin 4) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ i (roofPointSliceFourHornOverFiller a B F hF) = B.face i := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_injective a
  dsimp only [roofPointSliceFourHornOverFiller]
  rw [roofPointSliceThreeSimplexOfFourSimplex_face]
  rw [← horn.ι_ι_assoc (4 : Fin 5) i.castSucc (Fin.castSucc_ne_last i), hF]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face a B i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
