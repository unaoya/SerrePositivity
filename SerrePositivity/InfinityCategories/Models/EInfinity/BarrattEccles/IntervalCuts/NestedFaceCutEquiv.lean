module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCuts

/-!
模型。文献の定義との比較は後で
# 外側切断と内側面切断の二段切断への対応

概要：Berger–Fresse §2.2.6 の二段切断を、外側切断上の内側面切断の族として表示する。
方針：同じ切断点と Option を保持して部分型と依存対を組み替える。
規約：内側 arity 零と頂点入力の空和も含む。
使われ方：実際の二段余演算の反復和を合成辺成分と同じ有限添字へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：二段切断は外側非零切断と指定出力の内側面切断の依存対（BF §2.2.6）。
方針：外側の切断点と内側の Option を変更せず非零条件を組み替える。
規約：全 arity と全語次数を扱う。
使われ方：実際の右辺の反復切断和を一つの二段切断和へ移す。 -/
def faceCutEquiv (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k ≃
      Σ p : {p : Fin (m + 1 + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p.val k) where
  toFun a := ⟨⟨a.val.1, a.property.1⟩, ⟨a.val.2, a.property.2⟩⟩
  invFun a := ⟨(a.1.val, a.2.val), a.1.property, a.2.property⟩
  left_inv a := rfl
  right_inv a := by rcases a with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩; rfl

/-- 概要：依存対表示の内側出力を代入すると既存の全出力族に一致（BF §2.2.6）。
方針：none・some の両分岐で内側族の定義を評価する。
規約：残り色と挿入色の順序は既存の insertionFamily を使う。
使われ方：右辺の反復和と合成辺成分の実際の面テンソル値を揃える。 -/
lemma outputFamily_eq_faceCut (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) :
    a.outputFamily = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv u v k a).2.output) k := by
  rw [a.outputFamily_eq_insertion]
  rfl

/-- 概要：外側切断と内側面切断の反復和は二段切断の一重和（BF §2.2.6）。
方針：有限依存対の和と切断添字の同値による添字変更を合成する。
規約：値は任意の加法可換モノイドでよい。
使われ方：部分合成則の実際の右辺の有限和表示。 -/
lemma sum_faceCuts {M : Type*} [AddCommMonoid M]
    (F : (Σ p : {p : Fin (m + 1 + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p.val k)) → M) :
    (∑ p : {p : Fin (m + 1 + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
      ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p.val k), F ⟨p, a⟩) =
        ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k, F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv u v k a) := by
  rw [← Fintype.sum_sigma]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv u v k).sum_comp F |>.symm

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
