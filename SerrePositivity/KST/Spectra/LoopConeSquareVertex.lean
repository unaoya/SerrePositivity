module

public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

/-!
概要：cospan の錐を正方形へ移したときの、引き戻し頂点の厳密な計算。
方針：形状同型の錐頂点の像を Yoneda で評価する。
規約：値域の quasicategory 性は不要。使われ方：具体的な BF loop 対象の頂点の指定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

lemma coneSquare_vertex {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : JoinCone p) :
    squareVertex (coneSquare c) 0 0 = c.vertex := by
  have h : SSet.yonedaEquiv.symm
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) ≫ coneSquare c =
        joinInl (Δ[0] : SSet.{u}) (horn 2 2) ≫ c.val := by
    rw [← cospanConeSquareIso_initialPoint]
    change (joinInl (Δ[0] : SSet.{u}) (horn 2 2) ≫ cospanConeSquareIso.hom) ≫
      (cospanConeSquareIso.inv ≫ c.val) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hh := congrArg SSet.yonedaEquiv h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hh
  exact hh

end SerrePositivity.KST.Spectra
