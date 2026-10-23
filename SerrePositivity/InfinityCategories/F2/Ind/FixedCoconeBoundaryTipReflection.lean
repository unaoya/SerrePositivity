module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundarySliceReflection

/-!
概要：終点の厳密な正規化後にも、固定境界の比較を元の comma の全族へ反映する。
方針：同じ終点写像の等式を消去し、実証済みの全族の反映を使う。
規約：全余錐と両固定条件を保持。使われ方：区間の宇宙比較を戻した余錐の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 終点の同じ厳密な正規化の後で、元の comma の全族への反映を適用する。 -/
lemma nonempty_commaFunctorIso_of_fixedCoconeBoundaryIso_of_tip_eq
    {A X C : SSet.{u}} [Quasicategory X] [Quasicategory C]
    (p p' : (Δ[0] : SSet.{u}) ⟶ X) (hp : p = p') (b : A ⟶ X)
    (δ : C ⟶ X) (hδ : IsFullyFaithful δ)
    (f g : A ⟶ pullback δ (sliceOverProjection p'))
    (v w : (fixedCoconeBoundary p b) _⦋0⦌)
    (hv : v.val = functorVertex (sliceOverUncurry
      (f ≫ pullback.snd δ (sliceOverProjection p'))))
    (hw : w.val = functorVertex (sliceOverUncurry
      (g ≫ pullback.snd δ (sliceOverProjection p'))))
    (e : VertexIso v w) : Nonempty (FunctorIso f g) := by
  subst p'
  exact nonempty_commaFunctorIso_of_fixedCoconeBoundaryIso p b δ hδ f g v w hv hw e

end SerrePositivity.InfinityCategories.F2.Ind
