module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentInteriorSum

/-!
# 比較成分族の有限内部座標による表示

概要：比較成分族の各射を次数を指定した内部点成分へ同定し、内部集合の等式を移す。
方針：成分族の定義を評価し、部分集合の等式を消去する。
規約：端点と次数の証明は値に影響しない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の既存の dg 単体の方程式の各項の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：内部座標集合が等しければ標準成分は異種等号で一致する。
方針：集合の等式を消去する。
規約：次数は各集合の濃度の負として保持する。
使われ方：Kerodon 2.5.9（Tag 00SC） の削除・切断の成分の同定。 -/
lemma coherentCubeComponent_heq_of_set_eq {J : Type u} [LinearOrder J] {a b : J}
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S T : Finset (Set.Ioo a b)) (h : S = T) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab S) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab T) := by
  subst T
  rfl

/-- 概要：内部集合が等しければ同じ次数を指定した成分は等しい。
方針：集合の等式を消去し、次数の証明の一意性を使う。
規約：集合の構成に使う判定の実装には依存しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の native な集合の削除の表示をそろえる。 -/
lemma coherentCubeComponentAt_eq_of_set_eq {J : Type u} [LinearOrder J] {a b : J}
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S T : Finset (Set.Ioo a b)) (k : ℤ)
    (hk : k = -(S.card : ℤ)) (hl : k = -(T.card : ℤ)) (h : S = T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S k hk = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab T k hl := by
  subst T
  rfl

/-- 概要：比較成分族の射は同じ次数を指定した内部点成分である。
方針：成分族の hom の定義を評価する。
規約：次数の等式を明示的な引数に取り、通常の等号で述べる。
使われ方：HA 1.3.1.16 の微分公式の左辺を既存の hom へ合わせる。 -/
lemma coherentSimplexData_hom_eq_componentAt {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) (hab : a < b)
    (hdeg : k = -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).hom I a b k hI ha hb hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s (show ULift.up a < ULift.up b from hab)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior I a b) k hdeg := rfl

/-- 概要：比較成分族の射は等しい内部座標集合の標準成分と異種等号で一致する。
方針：定義からの異種等号に内部集合の等式による異種等号を合成する。
規約：射の次数の表現を変えずに比較できる。
使われ方：Kerodon 2.5.9（Tag 00SC） の rhs の削除・合成の各成分を内部座標へ移す。 -/
lemma coherentSimplexData_hom_heq_set {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) (hab : a < b)
    (T : Finset (Set.Ioo (ULift.up a : ULift.{u} (Fin (n + 1))) (ULift.up b)))
    (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior I a b = T) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).hom I a b k hI ha hb hk) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s
      (show ULift.up a < ULift.up b from hab) T) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_heq s I a b k hI ha hb hk).trans
    (coherentCubeComponent_heq_of_set_eq s (show ULift.up a < ULift.up b from hab) _ _ hT)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
