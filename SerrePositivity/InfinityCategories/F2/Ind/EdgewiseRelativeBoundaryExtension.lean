module

public import SerrePositivity.InfinityCategories.F2.Ind.EdgewiseWeightRelativeLift
public import SerrePositivity.InfinityCategories.F2.Ind.RangeCoverGluingOver
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseCoverDomain
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOneBoundary

/-!
概要：right fibration の edgewise の全境界と右端を、元の底の全図式上で延長する。
方針：境界面と右半分を底上で接合し、同じ領域の right anodyne 性を使う。
規約：Kan 全空間を仮定せず、指定した射影・境界・右半分を同時に保つ。
使われ方：元の right unstraightening の twisted arrow 比較の大域的構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 各境界面と右半分を保ち、同じ元の底の重みの図式上で延長できる。 -/
lemma exists_edgewiseRight_relative_weight_extension {E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision E)
    (e : (Δ[n + 1] : SSet.{u}) ⟶ E)
    (sq : CommSq a (boundary (n + 1)).ι (edgewiseRight E) e)
    (b : edgewiseWeight.obj ⦋n + 1⦌ ⟶ B)
    (he : e ≫ p = joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ b)
    (hf : ∀ i : Fin (n + 2), SSet.yonedaEquiv (boundary.ι i ≫ a) ≫ p =
      edgewiseWeight.map (SimplexCategory.δ i) ≫ b) :
    ∃ F : edgewiseWeight.obj ⦋n + 1⦌ ⟶ E,
      (∀ i : Fin (n + 2), edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      (joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = e) ∧ F ≫ p = b := by
  let X : Option (Fin (n + 2)) → SSet.{u} := fun
    | none => Δ[n + 1]
    | some _ => edgewiseWeight.obj ⦋n⦌
  let ι : ∀ i, X i ⟶ edgewiseWeight.obj ⦋n + 1⦌ := fun
    | none => joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]
    | some i => edgewiseWeight.map (SimplexCategory.δ i)
  let f : ∀ i, X i ⟶ E := fun
    | none => e
    | some i => SSet.yonedaEquiv (boundary.ι i ≫ a)
  have hcomp : ∀ (i j : Option (Fin (n + 2))) (d : SimplexCategoryᵒᵖ)
      (x : (X i).obj d) (y : (X j).obj d),
      (ι i).app d x = (ι j).app d y → (f i).app d x = (f j).app d y := by
    intro i j d x y hxy
    cases i with
    | none =>
      cases j with
      | none =>
        have heq : x = y := (mono_iff_injective
          ((joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d)).mp inferInstance hxy
        subst y
        rfl
      | some j => exact (edgewiseBoundaryFace_right_compatible a e sq j d y x hxy.symm).symm
    | some i =>
      cases j with
      | none => exact edgewiseBoundaryFace_right_compatible a e sq i d x y hxy
      | some j => exact edgewiseBoundaryFaces_compatible_all a i j d x y hxy
  obtain ⟨G, hG, hGp⟩ := exists_map_of_compatible_range_cover_over X ι f p b
    (fun i ↦ by cases i with | none => exact he | some i => exact hf i) hcomp
  let D : (edgewiseWeight.obj ⦋n + 1⦌).Subcomplex := ⨆ i, Subcomplex.range (ι i)
  have hD : edgewiseRightWeightDomain (n + 1) = D := by
    rw [edgewiseRightWeightDomain_eq_face_cover]
    apply le_antisymm
    · refine sup_le (le_iSup (fun j ↦ Subcomplex.range (ι j)) none) (iSup_le (fun i ↦ ?_))
      exact le_iSup (fun j ↦ Subcomplex.range (ι j)) (some i)
    · apply iSup_le
      intro i
      cases i with
      | none => exact le_sup_left
      | some i => exact le_trans (le_iSup (fun k : Fin (n + 2) ↦
          Subcomplex.range (edgewiseWeight.{u}.map (SimplexCategory.δ k))) i) le_sup_right
  obtain ⟨F, hF, hFp⟩ := edgewiseRightWeightDomain_relative_lift p (n + 1)
    (Subcomplex.homOfLE hD.le ≫ G) b (by rw [Category.assoc, hGp]; rfl)
  have hDF : D.ι ≫ F = G := by
    have h := congrArg (fun g ↦ Subcomplex.homOfLE hD.ge ≫ g) hF
    change D.ι ≫ F = Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le ≫ G at h
    have hid : Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le = 𝟙 (D : SSet.{u}) := rfl
    rwa [← Category.assoc, hid, Category.id_comp] at h
  have hcover : ∀ i, ι i ≫ F = f i := by
    intro i
    calc
      _ = (Subcomplex.lift (ι i) (le_iSup (fun j ↦ Subcomplex.range (ι j)) i) ≫ D.ι) ≫ F := by
        rw [Subcomplex.lift_ι]
      _ = f i := by rw [Category.assoc, hDF, hG i]
  exact ⟨F, fun i ↦ hcover (some i), hcover none, hFp⟩

end SerrePositivity.InfinityCategories.F2.Ind
