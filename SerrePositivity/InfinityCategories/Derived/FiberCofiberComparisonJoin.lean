module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonTriangles
public import SerrePositivity.InfinityCategories.Derived.SpanJoinFaces

/-! # 双対比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 余錐と元の fiber 余錐を結ぶ。
方針：span の join の二セル表示を使い、共通面と両端を照合する。
規約：同じ span 上の余錐の間の比較。使われ方：D7 の coslice 辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 上下の比較三単体は span の join の共通面で一致する。 -/
lemma fiberCofiberComparisonCells_compatible (g : B ⟶ D) (h : C ⟶ D) :
    SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (fiberCofiberComparisonLower g h) :
          (Δ[3] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm (fiberCofiberComparisonUpper g h) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (fiberCofiberComparison_common g h)

/-- Span の join 上の実際の比較写像。 -/
def fiberCofiberComparisonJoin (g : B ⟶ D) (h : C ⟶ D) :
    join (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ⟶ dgNerve S (Complex S) :=
  (spanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (fiberCofiberComparisonLower g h))
    (SSet.yonedaEquiv.symm (fiberCofiberComparisonUpper g h))
    (fiberCofiberComparisonCells_compatible g h)

/-- 左セルへの制限は下側比較三単体。 -/
lemma fiberCofiberComparisonJoin_left (g : B ⟶ D) (h : C ⟶ D) :
    spanJoinLeft 1 ≫ fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (fiberCofiberComparisonLower g h) :=
  (spanJoin_isPushout 1).inl_desc _ _ _

/-- 右セルへの制限は上側比較三単体。 -/
lemma fiberCofiberComparisonJoin_right (g : B ⟶ D) (h : C ⟶ D) :
    spanJoinRight 1 ≫ fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (fiberCofiberComparisonUpper g h) :=
  (spanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の始点は標準 cofiber 余錐。 -/
lemma fiberCofiberComparisonJoin_face_one (g : B ⟶ D) (h : C ⟶ D) :
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      fiberCofiberComparisonJoin g h =
        (standardCofiberCocone (pullbackProjectionB g h) (pullbackProjectionC g h)).val := by
  apply (spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc,
      fiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((fiberCofiberComparisonLower g h).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [fiberCofiberComparisonLower_face_three]
    change _ = spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ standardCofiberSquare _ _)
    rw [← Category.assoc, spanCoconeSquareIso_left, standardCofiberSquare_lower]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc,
      fiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((fiberCofiberComparisonUpper g h).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [fiberCofiberComparisonUpper_face_three]
    change _ = spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ standardCofiberSquare _ _)
    rw [← Category.assoc, spanCoconeSquareIso_right, standardCofiberSquare_upper]

/-- 比較写像の終点は元の標準 fiber 四角形の余錐。 -/
lemma fiberCofiberComparisonJoin_face_zero (g : B ⟶ D) (h : C ⟶ D) :
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      fiberCofiberComparisonJoin g h = (pushoutCocone (standardFiberSquare g h)).val := by
  apply (spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc,
      fiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((fiberCofiberComparisonLower g h).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [fiberCofiberComparisonLower_face_two]
    change _ = spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ standardFiberSquare g h)
    rw [← Category.assoc, spanCoconeSquareIso_left, standardFiberSquare_lower]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc,
      fiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((fiberCofiberComparisonUpper g h).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [fiberCofiberComparisonUpper_face_two]
    change _ = spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ standardFiberSquare g h)
    rw [← Category.assoc, spanCoconeSquareIso_right, standardFiberSquare_upper]

end SerrePositivity.InfinityCategories
