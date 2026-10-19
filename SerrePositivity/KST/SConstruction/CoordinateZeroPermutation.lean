module
public import SerrePositivity.KST.SConstruction.CoordinateZeroIso

/-! # 多単体的座標の置換による全零境界の保存
概要：独立な各方向の置換で、全零境界の有限合併が変わらないことを示す。
方針：各零方向の冪等作用を逆置換された方向の作用と比較し、全方向の合併へ移す。
規約：任意の多単体的図式で成立する。使われ方：最内側 S の座標移動と巡回交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 多方向の置換を全対角で実現すると元の対角と恒等成分で一致する。 -/
def coordinatePermutationDiagonalIso {r : ℕ} (p : Equiv.Perm (Fin r))
    (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙
      Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p ⋙ M) ≅
      simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M) := Iso.refl _

/-- 一方向の零自己射を置換すると、逆置換された方向の零自己射になる。 -/
lemma zeroDirectionsIndexEndomorphism_permutation {r : ℕ} (p : Equiv.Perm (Fin r))
    (i : Fin r) (d : SimplexCategoryᵒᵖ) :
    (Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p).map
        (zeroDirectionsIndexEndomorphism {i} (fun _ => d)) =
      zeroDirectionsIndexEndomorphism {p.symm i} (fun _ => d) := by
  funext j
  change zeroCoordinateEndomorphism (p j) (decide (p j ∈ ({i} : Finset (Fin r))))
      (fun _ => d) =
    zeroCoordinateEndomorphism j (decide (j ∈ ({p.symm i} : Finset (Fin r)))) (fun _ => d)
  have hb : decide (p j ∈ ({i} : Finset (Fin r))) =
      decide (j ∈ ({p.symm i} : Finset (Fin r))) := by
    simp only [Finset.mem_singleton]
    congr 1
    exact propext (p.eq_symm_apply).symm
  rw [hb]
  cases decide (j ∈ ({p.symm i} : Finset (Fin r))) <;> rfl

/-- 置換した図式の一つの零方向の像は、元の図式の逆置換した零方向の像。 -/
lemma coordinateZeroRange_permutation {r : ℕ} (p : Equiv.Perm (Fin r)) (i : Fin r)
    (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙
      Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p ⋙ M)).obj d) :
    x ∈ (coordinateZeroRange {i}
      (Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p ⋙ M)).obj d ↔
      x ∈ (coordinateZeroRange {p.symm i} M).obj d := by
  rw [mem_coordinateZeroRange_iff, mem_coordinateZeroRange_iff]
  simp only [coordinateZeroOperator_eq_map]
  change ((M.map ((Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p).map
    (zeroDirectionsIndexEndomorphism {i} (fun _ => d)))).app d x = x) ↔ _
  rw [zeroDirectionsIndexEndomorphism_permutation]
  rfl

/-- 全方向の零境界の有限合併は多方向の置換で厳密に保存される。 -/
lemma coordinateZeroBoundary_permutation {r : ℕ} (p : Equiv.Perm (Fin r))
    (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (coordinateZeroBoundary Finset.univ ∅
      (Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p ⋙ M)).image
        (coordinatePermutationDiagonalIso p M).hom = coordinateZeroBoundary Finset.univ ∅ M := by
  change (coordinateZeroBoundary Finset.univ ∅
    (Pi.comap (fun _ : Fin r => SimplexCategoryᵒᵖ) p ⋙ M)).image (𝟙 _) = _
  rw [Subcomplex.image_id]
  ext d x
  simp only [coordinateZeroBoundary, Finset.sup_eq_iSup, Finset.mem_univ, iSup_pos,
    Finset.insert_empty, Subfunctor.iSup_obj, Set.mem_iUnion, coordinateZeroRange_permutation]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨p.symm i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨p i, ?_⟩
    simpa only [p.symm_apply_apply] using hi

end SerrePositivity.KST.SConstruction
