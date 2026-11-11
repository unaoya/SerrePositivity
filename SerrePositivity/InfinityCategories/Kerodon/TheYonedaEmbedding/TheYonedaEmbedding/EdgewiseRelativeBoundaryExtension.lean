module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.EdgewiseWeightRelativeLift
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RangeCoverGluingOver
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseCoverDomain
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOneBoundary

/-!
概要：right fibration の edgewise の全境界と右端を、元の底の全図式上で延長する。
方針：境界面と右半分を底上で接合し、同じ領域の right anodyne 性を使う。
規約：Kan 全空間を仮定せず、指定した射影・境界・右半分を同時に保つ。
使われ方：元の right unstraightening の twisted arrow 比較の大域的構成。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 各境界面と右半分を保ち、同じ元の底の重みの図式上で延長できる。 -/
lemma exists_edgewiseRight_relative_weight_extension {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision E)
    (e : (Δ[n + 1] : SSet.{u}) ⟶ E)
    (sq : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight E) e)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ B)
    (he : e ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ b)
    (hf : ∀ i : Fin (n + 2), SSet.yonedaEquiv (boundary.ι i ≫ a) ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ b) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ E,
      (∀ i : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = e) ∧ F ≫ p = b := by
  let X : Option (Fin (n + 2)) → SSet.{u} := fun
    | none => Δ[n + 1]
    | some _ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌
  let ι : ∀ i, X i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ := fun
    | none => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]
    | some i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)
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
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d)).mp inferInstance hxy
        subst y
        rfl
      | some j => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a e sq j d y x hxy.symm).symm
    | some i =>
      cases j with
      | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a e sq i d x y hxy
      | some j => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFaces_compatible_all a i j d x y hxy
  obtain ⟨G, hG, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.exists_map_of_compatible_range_cover_over X ι f p b
    (fun i ↦ by cases i with | none => exact he | some i => exact hf i) hcomp
  let D : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).Subcomplex := ⨆ i, Subcomplex.range (ι i)
  have hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain (n + 1) = D := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain_eq_face_cover]
    apply le_antisymm
    · refine sup_le (le_iSup (fun j ↦ Subcomplex.range (ι j)) none) (iSup_le (fun i ↦ ?_))
      exact le_iSup (fun j ↦ Subcomplex.range (ι j)) (some i)
    · apply iSup_le
      intro i
      cases i with
      | none => exact le_sup_left
      | some i => exact le_trans (le_iSup (fun k : Fin (n + 2) ↦
          Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ k))) i) le_sup_right
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseRightWeightDomain_relative_lift p (n + 1)
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

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
