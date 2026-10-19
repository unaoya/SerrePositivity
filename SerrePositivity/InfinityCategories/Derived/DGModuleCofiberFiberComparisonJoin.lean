module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberComparisonTriangles
public import SerrePositivity.InfinityCategories.DGNerve.CospanJoinCells
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryTriangles

/-! # 比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 錐と標準 fiber 錐を結ぶ写像を作る。
方針：cospan の join の二セル表示と、各三単体の零面・一面を使う。
規約：二つの錐は同じ cospan を持つ。使われ方：β3 の実際の slice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 上下の比較三単体を貼るための共通面の一致。 -/
lemma dgModuleCofiberFiberComparisonCells_compatible (f : M ⟶ N) :
    SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonLower A D f) :
          (Δ[3] : SSet) ⟶ dgModuleNerve A D) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫
        SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonUpper A D f) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparison_common A D f)

/-- 二つの錐を結ぶ join 上の実際の単体的写像。 -/
def dgModuleCofiberFiberComparisonJoin (f : M ⟶ N) :
    join (Δ[1] : SSet) (SSet.horn 2 2) ⟶ dgModuleNerve A D :=
  (cospanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonLower A D f))
    (SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonUpper A D f))
    (dgModuleCofiberFiberComparisonCells_compatible A D f)

/-- 貼合せ写像の左セルは下側比較三単体。 -/
lemma dgModuleCofiberFiberComparisonJoin_left (f : M ⟶ N) :
    cospanJoinLeft 1 ≫ dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonLower A D f) :=
  (cospanJoin_isPushout 1).inl_desc _ _ _

/-- 貼合せ写像の右セルは上側比較三単体。 -/
lemma dgModuleCofiberFiberComparisonJoin_right (f : M ⟶ N) :
    cospanJoinRight 1 ≫ dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (dgModuleCofiberFiberComparisonUpper A D f) :=
  (cospanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の終点は標準 fiber 錐そのもの。 -/
lemma dgModuleCofiberFiberComparisonJoin_face_zero (f : M ⟶ N) :
    joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet)) ≫
        dgModuleCofiberFiberComparisonJoin A D f =
      (dgModuleFiberCone A D (moduleConeInr A D f)).val := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((dgModuleCofiberFiberComparisonLower A D f).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ dgModuleNerve A D) = _
    rw [dgModuleCofiberFiberComparisonLower_face_zero]
    exact (dgModuleFiberCone_left_triangle A D (moduleConeInr A D f)).symm
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((dgModuleCofiberFiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ dgModuleNerve A D) = _
    rw [dgModuleCofiberFiberComparisonUpper_face_zero]
    exact (dgModuleFiberCone_right_triangle A D (moduleConeInr A D f)).symm

/-- 比較写像の始点は元の標準 cofiber 正方形の錐。 -/
lemma dgModuleCofiberFiberComparisonJoin_face_one (f : M ⟶ N) :
    joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet)) ≫
        dgModuleCofiberFiberComparisonJoin A D f = (pullbackCone (dgModuleConeSquare A D f)).val
          := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((dgModuleCofiberFiberComparisonLower A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ dgModuleNerve A D) = _
    rw [dgModuleCofiberFiberComparisonLower_face_one]
    change _ = cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ dgModuleConeSquare A D f)
    rw [← Category.assoc, cospanConeSquareIso_left, dgModuleConeSquare_lower]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((dgModuleCofiberFiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ dgModuleNerve A D) = _
    rw [dgModuleCofiberFiberComparisonUpper_face_one]
    change _ = cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ dgModuleConeSquare A D f)
    rw [← Category.assoc, cospanConeSquareIso_right, dgModuleConeSquare_upper]

end SerrePositivity.InfinityCategories
