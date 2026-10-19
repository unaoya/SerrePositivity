module

public import SerrePositivity.InfinityCategories.DGNerve.JoinSimplexFaces
public import SerrePositivity.InfinityCategories.Core.Limit

/-!
概要：元の錐の辺を底の一区間で制限し、同じ三単体の四面を計算する。
方針：標準 join 同型の左右の面の式と、元の slice の辺の両端の等式を使う。
規約：底の図式と元の錐の辺全体を保持。使われ方：円評価錐の比較の Hom 正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.DGNerve
namespace SerrePositivity.KST.Spectra.ConeEdgeInterval

/-- 可変区間の二つの面を、同じ標準三単体の最初の二面へ戻す式。 -/
lemma leftFace (j : Fin 2) :
    stdSimplex.δ (j.castAdd 2) ≫ (joinStdSimplexIso.{u} 1 1).inv =
      (joinStdSimplexIso 0 1).inv ≫ joinMap (stdSimplex.δ j) (𝟙 Δ[1]) := by
  apply (cancel_mono (joinStdSimplexIso 1 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinStdSimplexIso_left_face, Iso.inv_hom_id_assoc]

/-- 底の区間の終点は、同じ標準三単体の二番目の面。 -/
lemma targetFace :
    stdSimplex.δ (2 : Fin 4) ≫ (joinStdSimplexIso.{u} 1 1).inv =
      (joinStdSimplexIso 1 0).inv ≫ joinMap (𝟙 Δ[1]) (stdSimplex.δ (0 : Fin 2)) := by
  apply (cancel_mono (joinStdSimplexIso 1 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinStdSimplexIso_right_last, Iso.inv_hom_id_assoc]
  rfl

/-- 底の区間の始点との join は、同じ標準三単体の最後の面。 -/
lemma sourceFace_hom :
    joinMap (𝟙 (Δ[1] : SSet.{u})) (stdSimplex.δ (1 : Fin 2)) ≫
      (joinStdSimplexIso 1 1).hom =
    (joinStdSimplexIso 1 0).hom ≫ stdSimplex.δ (3 : Fin 4) := by
  apply join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.id_comp, joinStdSimplexIso_inl,
      ← Category.assoc, joinStdSimplexIso_inl]
    change stdSimplex.map _ = stdSimplex.map _ ≫ stdSimplex.map _
    rw [← stdSimplex.map_comp]
    apply congrArg stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  · rw [← Category.assoc, joinInr_joinMap, Category.assoc, joinStdSimplexIso_inr,
      ← Category.assoc, joinStdSimplexIso_inr]
    change stdSimplex.map _ ≫ stdSimplex.map _ = stdSimplex.map _ ≫ stdSimplex.map _
    rw [← stdSimplex.map_comp, ← stdSimplex.map_comp]
    apply congrArg stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i
    rfl

/-- 底の区間の始点は、同じ標準三単体の最後の面。 -/
lemma sourceFace :
    stdSimplex.δ (3 : Fin 4) ≫ (joinStdSimplexIso.{u} 1 1).inv =
      (joinStdSimplexIso 1 0).inv ≫ joinMap (𝟙 Δ[1]) (stdSimplex.δ (1 : Fin 2)) := by
  apply (cancel_mono (joinStdSimplexIso 1 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [sourceFace_hom, Iso.inv_hom_id_assoc]

variable {K X : SSet.{u}} {p : K ⟶ X} {c d : JoinCone p}

/-- 元の錐の元の一区間上の三角形。 -/
def triangleMap (c : JoinCone p) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  (joinStdSimplexIso 0 1).inv ≫ joinMap (𝟙 Δ[0]) a ≫ c.val

/-- 元の錐の辺を、底の元の一区間で読んだ同じ三単体。 -/
def simplexMap (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    (Δ[3] : SSet.{u}) ⟶ X :=
  (joinStdSimplexIso 1 1).inv ≫ joinMap (𝟙 Δ[1]) a ≫ e.edge.val

/-- 元の錐の辺を、底の元の一点で読んだ同じ三角形。 -/
def vertexFaceMap (e : (sliceOver p).Edge c d) (b : (Δ[0] : SSet.{u}) ⟶ K) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  (joinStdSimplexIso 1 0).inv ≫ joinMap (𝟙 Δ[1]) b ≫ e.edge.val

/-- 同じ三単体の零面は、元の終点の錐の同じ一区間上の三角形。 -/
lemma simplexMap_zero (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    stdSimplex.δ (0 : Fin 4) ≫ simplexMap e a = triangleMap d a := by
  have hj := leftFace.{u} (0 : Fin 2)
  change stdSimplex.δ (0 : Fin 4) ≫ _ = _ at hj
  rw [simplexMap, ← Category.assoc, hj]
  have hc : joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[1]) ≫ joinMap (𝟙 Δ[1]) a =
      joinMap (𝟙 Δ[0]) a ≫ joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 K) := by
    rw [← joinMap_comp, ← joinMap_comp]
    simp only [Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← Category.assoc _ _ e.edge.val, hc, Category.assoc]
  have he := congrArg Subtype.val e.tgt_eq
  change joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 K) ≫ e.edge.val = d.val at he
  rw [he]
  rfl

/-- 同じ三単体の一面は、元の始点の錐の同じ一区間上の三角形。 -/
lemma simplexMap_one (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    stdSimplex.δ (1 : Fin 4) ≫ simplexMap e a = triangleMap c a := by
  have hj := leftFace.{u} (1 : Fin 2)
  change stdSimplex.δ (1 : Fin 4) ≫ _ = _ at hj
  rw [simplexMap, ← Category.assoc, hj]
  have hc : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[1]) ≫ joinMap (𝟙 Δ[1]) a =
      joinMap (𝟙 Δ[0]) a ≫ joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 K) := by
    rw [← joinMap_comp, ← joinMap_comp]
    simp only [Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← Category.assoc _ _ e.edge.val, hc, Category.assoc]
  have he := congrArg Subtype.val e.src_eq
  change joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 K) ≫ e.edge.val = c.val at he
  rw [he]
  rfl

/-- 同じ三単体の二面は、元の底の区間の終点上の三角形。 -/
lemma simplexMap_two (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    stdSimplex.δ (2 : Fin 4) ≫ simplexMap e a =
      vertexFaceMap e (stdSimplex.δ (0 : Fin 2) ≫ a) := by
  rw [simplexMap, ← Category.assoc, targetFace]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← joinMap_comp]
  simp only [Category.comp_id]

/-- 同じ三単体の三面は、元の底の区間の始点上の三角形。 -/
lemma simplexMap_three (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    stdSimplex.δ (3 : Fin 4) ≫ simplexMap e a =
      vertexFaceMap e (stdSimplex.δ (1 : Fin 2) ≫ a) := by
  rw [simplexMap, ← Category.assoc, sourceFace]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← joinMap_comp]
  simp only [Category.comp_id]

/-- 同じ三単体の最初の辺は、元の錐の比較辺の apex 方向そのもの。 -/
lemma simplexMap_apex_edge (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫ simplexMap e a =
      joinInl (Δ[1] : SSet.{u}) K ≫ e.edge.val := by
  have h : joinInl (Δ[1] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 1 1).hom =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) := by
    rw [joinStdSimplexIso_inl]
    apply SSet.yonedaEquiv.injective
    decide
  rw [← h, simplexMap, Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc, joinInl_joinMap, Category.id_comp]

/-- 同じ三単体の最後の辺は、元の固定図式の同じ底の区間そのもの。 -/
lemma simplexMap_base_edge (e : (sliceOver p).Edge c d) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫ simplexMap e a = a ≫ p := by
  have h : joinInr (Δ[1] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 1 1).hom =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) := by
    rw [joinStdSimplexIso_inr]
    apply SSet.yonedaEquiv.injective
    decide
  rw [← h, simplexMap, Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc, joinInr_joinMap, Category.assoc, e.edge.property]

end SerrePositivity.KST.Spectra.ConeEdgeInterval
