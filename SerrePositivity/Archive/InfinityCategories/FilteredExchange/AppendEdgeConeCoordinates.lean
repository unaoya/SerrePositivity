module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendConeReassociation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：追加錐の二終点を元の実区間として読む座標。
方針：点二つの join の標準同型と元の結合同型を使う。
規約：全パラメータ写像に自然。使われ方：指定射上の実 slice 族の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実区間を、追加錐の二つの終点として読む同じ座標。 -/
def appendEdgeConeCoordinates (A : SSet.{u}) :
    join A Δ[1] ⟶ join (join A Δ[0]) Δ[0] :=
  joinMap (𝟙 A) (joinStdSimplexIso 0 0).inv ≫ (stableJoinAssociator A Δ[0] Δ[0]).inv

/-- 実区間の二終点への座標は、元の全係数の写像に自然。 -/
lemma appendEdgeConeCoordinates_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    joinMap f (𝟙 Δ[1]) ≫ appendEdgeConeCoordinates B =
      appendEdgeConeCoordinates A ≫ joinMap (joinMap f (𝟙 Δ[0])) (𝟙 Δ[0]) := by
  have h : joinMap f (𝟙 (Δ[1] : SSet.{u})) ≫
      joinMap (𝟙 B) (joinStdSimplexIso 0 0).inv =
    joinMap (𝟙 A) (joinStdSimplexIso 0 0).inv ≫ joinMap f (𝟙 (join Δ[0] Δ[0])) := by
    simp only [← joinMap_comp, Category.id_comp, Category.comp_id]
  rw [appendEdgeConeCoordinates, ← Category.assoc, h, Category.assoc,
    appendConeAssociator_inv_naturality]
  rfl

/-- 元の実区間全体は、同じ追加錐の二つの終点全体として回収される。 -/
lemma appendEdgeConeCoordinates_inr (A : SSet.{u}) :
    joinInr A Δ[1] ≫ appendEdgeConeCoordinates A =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (joinInr A Δ[0]) (𝟙 Δ[0]) := by
  rw [appendEdgeConeCoordinates, ← Category.assoc, joinInr_joinMap, Category.assoc,
    appendConeAssociator_rightPair_inv]

/-- 元の実区間の始点を残すと、元の全錐を含む前面そのものになる。 -/
lemma appendEdgeConeCoordinates_start (A : SSet.{u}) :
    joinMap (𝟙 A) (stdSimplex.δ (1 : Fin 2)) ≫ appendEdgeConeCoordinates A =
      joinInl (join A Δ[0]) Δ[0] := by
  have h : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      (joinStdSimplexIso 0 0).inv = joinInl Δ[0] Δ[0] := by
    change stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      (joinStdSimplexIso 0 0).inv = joinInl Δ[0] Δ[0]
    rw [← PinchedHom.front_zero, ← joinStdSimplexIso_rightPoint_inl,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [appendEdgeConeCoordinates, ← Category.assoc, ← joinMap_comp, Category.id_comp, h,
    ← stableJoinAssociator_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.F2
