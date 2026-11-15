module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionReindexing
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions

/-!
概要：再添字付けの同じ頂点へ写る点で、水平分解の切れ目と左右の長さを照合する。
方針：元の射が恒等射の輸送となることを、切れ目の可換条件に適用する。
規約：左右の対象の等式を仮定しない。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：対象の等式の輸送の射の共通表示は恒等射と異種等式で一致する。
方針：同じ対象に戻して共通表示の恒等則を使う。
規約：実Homの対象の等式。使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の比較。 -/
lemma walkingAdjunctionOrderHom_eqToHom_heq {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (h : A = B) :
    HEq (walkingAdjunctionOrderHom (eqToHom h))
      (OrderHom.id : Fin (walkingAdjunctionOrdinalCard X Y A) →o
        Fin (walkingAdjunctionOrdinalCard X Y A)) := by
  subst B
  exact heq_of_eq (walkingAdjunctionOrderHom_id X Y A)

/-- 概要：元の全射が恒等射の輸送なら切れ目の座標は変わらない。
方針：plusは実区間表示、minusは元の射の恒等則を可換条件へ適用する。
規約：型の個数の輸送を明示する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCut_coordinate_eq_of_identity {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    {i j : Fin (n + 1)} (hij : i ≤ j) (he : F.obj i = F.obj j)
    (hf : F.map (homOfLE hij) = eqToHom he) :
    walkingAdjunctionCutCoordinate a i = walkingAdjunctionCutCoordinate a j := by
  have hcard := congrArg (walkingAdjunctionOrdinalCard X Y) he
  have hp := (heq_of_eq (congrArg (fun f => walkingAdjunctionOrderHom f) hf)).trans
    (walkingAdjunctionOrderHom_eqToHom_heq he)
  cases M
  · have ht := (ordinalIntervalMap_heq rfl hcard.symm hp).trans
      (heq_of_eq (ordinalIntervalMap_id (walkingAdjunctionOrdinalCard X Y (F.obj i))))
    let z := (Fin.castOrderIso (congrArg (fun k => k + 1) hcard.symm)) (a.value j)
    have hv := ordinalOrderHom_heq_val (congrArg (fun k => k + 1) hcard.symm)
      rfl _ _ ht (a.value j) z rfl
    have hn := congrArg Fin.val (a.naturality hij)
    exact hn.symm.trans hv
  · have hv := ordinalOrderHom_heq_val rfl hcard.symm _ _ hp (a.value i) (a.value i) rfl
    have hn := congrArg Fin.val (a.naturality hij)
    exact hv.symm.trans hn

/-- 概要：恒等射の輸送で結ばれた二頂点では、水平分解の左因子の長さは同じ。
方針：切れ目の座標の一致と順位・長さの照合を使う。
規約：左因子の対象の一致を仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.left_length_eq_of_identity {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}
    (a : WalkingAdjunctionFactorization F) {i j : Fin (n + 1)} (hij : i ≤ j)
    (he : F.obj i = F.obj j) (hf : F.map (homOfLE hij) = eqToHom he) :
    walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X a.middle (a.left.obj j) := by
  have hc := walkingAdjunctionCut_coordinate_eq_of_identity a.cut hij he hf
  have hi := a.cut_rank i
  have hj := a.cut_rank j
  unfold walkingAdjunctionCutRank at hi hj
  omega

/-- 概要：再添字付けの同じ頂点へ写る点で、実分解の左因子の長さは一致する。
方針：二点の全順序と、薄い順序圏の射が対象の等式の輸送となることを使う。
規約：全順序関手を扱う。使われ方：Riehl–Verity Proposition 3.1.10 の退化。 -/
lemma WalkingAdjunctionFactorization.left_length_eq_of_reindex_fiber {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (a : WalkingAdjunctionFactorization (P ⋙ F))
    {i j : Fin (m + 1)} (he : P.obj i = P.obj j) :
    walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X a.middle (a.left.obj j) := by
  have haux {i j : Fin (m + 1)} (hij : i ≤ j) (he : P.obj i = P.obj j) :
      (P ⋙ F).map (homOfLE hij) = eqToHom (congrArg F.obj he) := by
    have hp : P.map (homOfLE hij) = eqToHom he := Subsingleton.elim _ _
    exact (congrArg (fun f => F.map f) hp).trans (eqToHom_map F he)
  rcases le_total i j with hij | hji
  · exact a.left_length_eq_of_identity hij (congrArg F.obj he) (haux hij he)
  · exact (a.left_length_eq_of_identity hji (congrArg F.obj he.symm) (haux hji he.symm)).symm

/-- 概要：再添字付けの同じ頂点へ写る点で、右因子の長さも一致する。
方針：左因子の長さの一致と全水平合成の長さの加法則を使う。
規約：右因子の対象の一致を仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.right_length_eq_of_reindex_fiber {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (a : WalkingAdjunctionFactorization (P ⋙ F))
    {i j : Fin (m + 1)} (he : P.obj i = P.obj j) :
    walkingAdjunctionVertexLength a.middle Y (a.right.obj i) =
      walkingAdjunctionVertexLength a.middle Y (a.right.obj j) := by
  have hl := a.left_length_eq_of_reindex_fiber P F he
  have hi := congrArg (walkingAdjunctionVertexLength X Y) (CategoryTheory.Functor.congr_obj a.fac i)
  have hj := congrArg (walkingAdjunctionVertexLength X Y) (CategoryTheory.Functor.congr_obj a.fac j)
  have ht := congrArg (walkingAdjunctionVertexLength X Y) (congrArg F.obj he)
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod'_obj,
    walkingAdjunctionVertexLength_comp] at hi hj
  omega

end SerrePositivity.InfinityCategories.HA.Monads
