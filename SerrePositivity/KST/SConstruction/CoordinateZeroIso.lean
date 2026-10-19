module
public import SerrePositivity.KST.SConstruction.CoordinateZeroBoundary

/-! # 多単体的同型による全零境界の保存
概要：任意の多単体的自然同型は、各零方向の像とその有限合併を厳密に対応させる。
方針：零方向の包含との自然性を対角へ移し、同型による全射性で range を比較する。
規約：可縮性や Kan 性を仮定しない。使われ方：S₁ 交換を元の境界商へ降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 零方向の包含は全多単体的自然変換と厳密に可換。 -/
lemma coordinateZeroInclusion_naturality {r : ℕ} (s : Finset (Fin r))
    {M N : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (f : M ⟶ N) :
    coordinateZeroInclusion s M ≫ simplicialDiagonalFunctor.map
        (Functor.whiskerLeft (multiIndexDiagonal r) f) =
      simplicialDiagonalFunctor.map
        (Functor.whiskerLeft (multiIndexDiagonal r ⋙ zeroDirectionsIndex s) f) ≫
          coordinateZeroInclusion s N := by
  change simplicialDiagonalFunctor.map (coordinateZeroDiagramMap s M) ≫
      simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r) f) =
    simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r ⋙ zeroDirectionsIndex s) f) ≫
      simplicialDiagonalFunctor.map (coordinateZeroDiagramMap s N)
  rw [← simplicialDiagonalFunctor.map_comp, ← simplicialDiagonalFunctor.map_comp]
  congr 1
  apply NatTrans.ext
  funext d
  exact f.naturality ((zeroDirectionsIndexNat s).app ((multiIndexDiagonal r).obj d))

/-- 全多単体的同型は各零方向の像を相手の同じ零方向の像へ全射に写す。 -/
lemma coordinateZeroRange_image_iso {r : ℕ} (s : Finset (Fin r))
    {M N : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (e : M ≅ N) :
    (coordinateZeroRange s M).image (simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r) e.hom)) = coordinateZeroRange s N := by
  change (Subcomplex.range (coordinateZeroInclusion s M)).image _ = _
  rw [← Subcomplex.range_comp, coordinateZeroInclusion_naturality,
    Subcomplex.range_comp]
  have : IsIso (simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r ⋙ zeroDirectionsIndex s) e.hom)) :=
    inferInstance
  rw [Subcomplex.range_eq_top, Subcomplex.image_top]
  rfl

/-- 全多単体的同型は零境界の全有限合併を厳密に対応させる。 -/
lemma coordinateZeroBoundary_image_iso {r : ℕ} (s t : Finset (Fin r))
    {M N : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (e : M ≅ N) :
    (coordinateZeroBoundary s t M).image (simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r) e.hom)) = coordinateZeroBoundary s t N := by
  simp only [coordinateZeroBoundary, Finset.sup_eq_iSup]
  rw [Subcomplex.image_iSup]
  apply iSup_congr
  intro i
  by_cases hi : i ∈ s
  · simpa only [iSup_pos hi] using coordinateZeroRange_image_iso (insert i t) e
  · ext d x
    simp [hi, Subcomplex.image]

end SerrePositivity.KST.SConstruction
