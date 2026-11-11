module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroTerminal
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroInitialExtension

/-! # 零複体は dg nerve の始対象

概要：零複体を最初の頂点に持つ任意の正次元境界を直接充填する。
方針：指定境界の後続面に零頂点を加え、零始域の外延性で全ての面を比較する。
規約：HTT Definition 1.2.12.3 の双対、HA Construction 1.3.1.6。使われ方：N7b の零始対象。

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

/-- 概要：最初の頂点を飛ばす面は succ による後続制限。
方針：零番目の面の順序埋め込みを評価する。
規約：HA Construction 1.3.1.6。使われ方：零頂点追加の後続面の式との接続。 -/
lemma δ_zero_pullback {D : Type v} [DGCategory A D] {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 s = s.pullback (Fin.succOrderEmb (n + 1)).toOrderHom := by
  rfl

/-- 概要：境界の最初の頂点が零なら、最初の頂点を含む全ての面の始域も零。
方針：面の始点が同じ大域頂点に写ることと、境界の端点条件を使う。
規約：HTT §1.2.12 の双対。使われ方：各面への零始域の外延性の適用。 -/
lemma BoundaryData.face_first_obj (Z : Complex A) {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z))
    (j : Fin (n + 2)) (hj : j ≠ 0) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b j).obj 0 = Z := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face_vertex b j 0
  rw [Fin.succAbove_ne_zero_zero hj, hb, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 0 => s.obj 0) h

/-- 概要：後続面へ零頂点を加えた単体の全ての面は指定境界の面に一致する。
方針：最初の面は構成の式、他の面は零始域と共通の後続面の一致で比較する。
規約：HTT §1.2.12 の双対。使われ方：零始対象の直接の境界充填。 -/
lemma prependZero_boundary_face (Z : Complex A) (hZ : IsZero Z) {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z))
    (j : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero Z hZ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 0)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b j := by
  by_cases hj : j = 0
  · subst j
    rw [δ_zero_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero_back]
  · cases n with
    | zero =>
      have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero Z hZ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 0))).obj 0 =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 1).obj 0
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.δ_obj]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero Z hZ _).obj 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 1).obj 0
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero_first]
      exact (BoundaryData.face_first_obj Z b hb 1 hj).symm
    | succ n =>
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext_of_zero_first Z hZ
      · rw [← δ_zero_pullback, ← δ_zero_pullback]
        rw [SSet.δ_comp_δ_apply (Fin.zero_le j), Fin.castSucc_zero,
          δ_zero_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero_back]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face_back b j).symm
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.δ_obj, Fin.succ_succAbove_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero_first]
      · exact BoundaryData.face_first_obj Z b hb _ (Fin.succ_ne_zero j)

/-- 概要：零複体の頂点は複体 dg nerve の始対象。
方針：任意の正次元境界の後続面へ零頂点を加え、全ての面の一致で境界を貼り合わせる。
規約：HTT Definition 1.2.12.3 の双対。使われ方：N7b、零図式の余極限と後続の cofiber。
-/
lemma isInitialVertex_of_isZero (Z : Complex A) (hZ : IsZero Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z) := by
  intro n b hb
  refine ⟨SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.prependZero Z hZ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face b 0)), ?_⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    prependZero_boundary_face Z hZ b hb j, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.face, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
