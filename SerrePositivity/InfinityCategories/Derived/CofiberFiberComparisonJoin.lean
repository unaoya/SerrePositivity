module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonTriangles
public import SerrePositivity.InfinityCategories.DGNerve.CospanJoinCells
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryTriangles

/-! # 比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 錐と標準 fiber 錐を結ぶ写像を作る。
方針：cospan の join の二セル表示と、各三単体の零面・一面を使う。
規約：二つの錐は同じ cospan を持つ。使われ方：D7 の実際の slice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 上下の比較三単体を貼るための共通面の一致。 -/
lemma cofiberFiberComparisonCells_compatible (f : A ⟶ B) (g : A ⟶ C) :
    SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (cofiberFiberComparisonLower f g) :
          (Δ[3] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫
        SSet.yonedaEquiv.symm (cofiberFiberComparisonUpper f g) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (cofiberFiberComparison_common f g)

/-- 二つの錐を結ぶ join 上の実際の単体的写像。 -/
def cofiberFiberComparisonJoin (f : A ⟶ B) (g : A ⟶ C) :
    join (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ⟶ dgNerve S (Complex S) :=
  (cospanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (cofiberFiberComparisonLower f g))
    (SSet.yonedaEquiv.symm (cofiberFiberComparisonUpper f g))
    (cofiberFiberComparisonCells_compatible f g)

/-- 貼合せ写像の左セルは下側比較三単体。 -/
lemma cofiberFiberComparisonJoin_left (f : A ⟶ B) (g : A ⟶ C) :
    cospanJoinLeft 1 ≫ cofiberFiberComparisonJoin f g =
      SSet.yonedaEquiv.symm (cofiberFiberComparisonLower f g) :=
  (cospanJoin_isPushout 1).inl_desc _ _ _

/-- 貼合せ写像の右セルは上側比較三単体。 -/
lemma cofiberFiberComparisonJoin_right (f : A ⟶ B) (g : A ⟶ C) :
    cospanJoinRight 1 ≫ cofiberFiberComparisonJoin f g =
      SSet.yonedaEquiv.symm (cofiberFiberComparisonUpper f g) :=
  (cospanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の終点は標準 fiber 錐そのもの。 -/
lemma cofiberFiberComparisonJoin_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
        cofiberFiberComparisonJoin f g =
      (standardFiberCone (pushoutInclusionB f g) (pushoutInclusionC f g)).val := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      cofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((cofiberFiberComparisonLower f g).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [cofiberFiberComparisonLower_face_zero]
    exact (standardFiberCone_left_triangle _ _).symm
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      cofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((cofiberFiberComparisonUpper f g).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [cofiberFiberComparisonUpper_face_zero]
    exact (standardFiberCone_right_triangle _ _).symm

/-- 比較写像の始点は元の標準 cofiber 正方形の錐。 -/
lemma cofiberFiberComparisonJoin_face_one (f : A ⟶ B) (g : A ⟶ C) :
    joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
        cofiberFiberComparisonJoin f g = (pullbackCone (standardCofiberSquare f g)).val := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      cofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((cofiberFiberComparisonLower f g).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [cofiberFiberComparisonLower_face_one]
    change _ = cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ standardCofiberSquare f g)
    rw [← Category.assoc, cospanConeSquareIso_left, standardCofiberSquare_lower]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      cofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((cofiberFiberComparisonUpper f g).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [cofiberFiberComparisonUpper_face_one]
    change _ = cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ standardCofiberSquare f g)
    rw [← Category.assoc, cospanConeSquareIso_right, standardCofiberSquare_upper]

end SerrePositivity.InfinityCategories
