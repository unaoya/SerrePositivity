module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroExtensionality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation

/-! # 零複体は dg nerve の終対象

概要：零複体を最後の頂点に持つ任意の正次元境界を直接充填する。
方針：境界の先頭面に零頂点を加え、各面の零終端と外延性で指定境界との一致を示す。
規約：HTT Definition 1.2.12.3、HA Construction 1.3.1.6。使われ方：N7b の零終対象。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：最終点を飛ばす面は castSucc による先頭制限。
方針：面の順序埋め込みを最終点の場合で評価する。
規約：HA Construction 1.3.1.6。使われ方：零頂点追加の先頭面の式との接続。 -/
lemma δ_last_pullback {D : Type v} [DGCategory A D] {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ (Fin.last (n + 1)) s = s.pullback Fin.castSuccOrderEmb.toOrderHom := by
  change s.pullback (Fin.last (n + 1)).succAboveOrderEmb.toOrderHom = _
  congr 1
  apply DFunLike.ext
  intro i
  exact Fin.succAbove_last_apply i

/-- 概要：境界の最後の頂点が零なら、最後の頂点を含む全ての面の終端も零。
方針：面の終端が同じ大域頂点に写ることと、境界の端点条件を使う。
規約：HTT §1.2.12。使われ方：各面への零終端の外延性の適用。 -/
lemma BoundaryData.face_last_obj (Z : Complex A) {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z))
    (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b j).obj (Fin.last n) = Z := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face_vertex b j (Fin.last n)
  rw [Fin.succAbove_ne_last_last hj, hb, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 0 => s.obj 0) h

/-- 概要：先頭面へ零頂点を加えた単体の全ての面は、指定境界の面に一致する。
方針：最終面は構成の式、他の面は零終端と共通の先頭面の一致で比較する。
規約：HTT §1.2.12。使われ方：零終対象の直接の境界充填。 -/
lemma appendZero_boundary_face (Z : Complex A) (hZ : IsZero Z) {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z))
    (j : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero Z hZ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b (Fin.last (n + 1)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b j := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    rw [δ_last_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero_front]
  · cases n with
    | zero =>
      have hj0 : j = 0 := by fin_cases j <;> simp_all
      subst j
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero Z hZ _)).obj 0 = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.δ_obj]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero Z hZ _).obj (Fin.last 1) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 0).obj (Fin.last 0)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero_last]
      exact (BoundaryData.face_last_obj Z b hb 0 hj).symm
    | succ n =>
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext_of_zero_last Z hZ
      · rw [← δ_last_pullback, ← δ_last_pullback]
        rw [← SSet.δ_comp_δ_apply (Fin.le_last j), Fin.succ_last,
          δ_last_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero_front]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face_front b j).symm
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.δ_obj, Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero_last]
      · exact BoundaryData.face_last_obj Z b hb _ (Fin.castSucc_ne_last j)

/-- 概要：零複体の頂点は複体 dg nerve の終対象。
方針：任意の正次元境界の先頭面へ零頂点を加え、全ての面の一致で境界を貼り合わせる。
規約：HTT Definition 1.2.12.3。使われ方：N7b、零図式の極限と fiber の錐。
-/
lemma isTerminalVertex_of_isZero (Z : Complex A) (hZ : IsZero Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z) := by
  intro n b hb
  refine ⟨SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.appendZero Z hZ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b (Fin.last (n + 1)))), ?_⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    appendZero_boundary_face Z hZ b hb j, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
