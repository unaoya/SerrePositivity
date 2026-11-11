module

public import SerrePositivity.KST.Comparison.CylinderBoundary
public import SerrePositivity.KST.Comparison.CartesianTensorSquare

/-!
# 円筒の両端点の引き戻し正方形

概要：中央の対象の任意の射に対して、両端点の包含の自然性の正方形は厳密な引き戻しである。
方針：境界への同型の自然性と、独立した二因子の射の引き戻しを使う。
規約：Segal 1974 Lemma 1.7 の厳密な貼り合わせの中央の仮定。
使われ方：二重写像円筒の van Kampen の立方体の後ろの面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

/--
概要：零次標準単体との積への逆同型は対象の射に関して自然である。
方針：第一射影との合成で打ち消し、直積の自然性を使う。
規約：境界への余積の同型の自然性の補助。
使われ方：二つの端点の包含の自然性。
-/
@[reassoc] theorem simplexZeroTensorIso_inv_naturality {C C' : SSet.{u}} (c : C ⟶ C') :
    (simplexZeroTensorIso C).inv ≫ (c ▷ Δ[0]) = c ≫ (simplexZeroTensorIso C').inv := by
  apply (cancel_mono (simplexZeroTensorIso C').hom).mp
  have hn : (c ▷ Δ[0]) ≫ (simplexZeroTensorIso C').hom = (simplexZeroTensorIso C).hom ≫ c :=
    whiskerRight_fst c _
  simp only [Category.assoc]
  rw [hn]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/--
概要：円筒の端点の余積と境界への同型は対象の射に関して自然である。
方針：余積の二成分で単位の逆同型の自然性と二因子の作用の交換を使う。
規約：二重写像円筒の中央の正方形を境界の直積へ移す。
使われ方：両端点の正方形の引き戻し性。
-/
@[reassoc] theorem cylinderBoundaryIso_naturality {C C' : SSet.{u}} (c : C ⟶ C') :
    coprod.map c c ≫ (cylinderBoundaryIso C').hom =
      (cylinderBoundaryIso C).hom ≫ (c ▷ (SSet.boundary.{u} 1)) := by
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, cylinderBoundaryIso_inl, cylinderBoundaryIso_inl_assoc]
    rw [← simplexZeroTensorIso_inv_naturality_assoc, whisker_exchange]
  · simp only [coprod.inr_map_assoc, cylinderBoundaryIso_inr, cylinderBoundaryIso_inr_assoc]
    rw [← simplexZeroTensorIso_inv_naturality_assoc, whisker_exchange]

/--
概要：円筒の両端点の自然性の四角形は任意の中央の射に対して厳密な引き戻しである。
方針：境界への同型の正方形と直積の引き戻し正方形を横に貼り合わせる。
規約：Segal Lemma 1.7 の厳密な二重写像円筒の後ろの面。
使われ方：van Kampen の立方体の第一の引き戻し条件を仮定なしで満たす。
-/
theorem cylinderEndpoints_isPullback {C C' : SSet.{u}} (c : C ⟶ C') :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map c c) (c ▷ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') := by
  have h₁ : IsPullback (cylinderBoundaryIso C).hom (coprod.map c c)
      (c ▷ (SSet.boundary.{u} 1)) (cylinderBoundaryIso C').hom :=
    IsPullback.of_horiz_isIso ⟨(cylinderBoundaryIso_naturality c).symm⟩
  have h := h₁.paste_horiz (cartesianTensorSquare_isPullback c (SSet.boundary.{u} 1).ι)
  simpa only [← cylinderEndpoints_factor] using h

end SerrePositivity.KST.Comparison
