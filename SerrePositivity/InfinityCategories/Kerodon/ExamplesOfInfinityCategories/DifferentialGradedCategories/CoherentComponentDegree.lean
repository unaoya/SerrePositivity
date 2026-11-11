module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathSplitComposition

/-!
# 次数を指定した coherent 単体の成分

概要：内部点数の負の次数の成分を、等しいと証明された任意の次数で取り出す。
方針：次数の等式を消去して既存の立方体評価を返し、異種等号で標準成分と比較する。
規約：次数の証明は値に影響せず、追加の符号もない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の dg 単体の方程式を同じ次数の型で記述する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：濃度を別の自然数で表示した降順番号付けは元の番号付けと異種等号で一致する。
方針：濃度の等式を消去する。
規約：有限集合の元の順序を変えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の番号付けの次数表示の移送。 -/
lemma descendingEnumeration_heq_of_card {A : Type u} [LinearOrder A]
    (S : Finset A) {n : ℕ} (h : S.card = n) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) (Fin.revPerm.trans (S.orderIsoOfFin h).toEquiv) := by
  subst n
  rfl

/-- 概要：次数と番号付けを等式で移送しても立方体評価は異種等号で一致する。
方針：次数の等式と番号付けの異種等号を消去する。
規約：標準 Hom への射は同じものを使う。
使われ方：HA 1.3.1.16 の次数を指定した成分への評価の移送。 -/
lemma cubeEvaluation_heq_of_enumeration {T : Type u} {m n : ℕ} (h : m = n)
    (e : Fin m ≃ T) (f : Fin n ≃ T) (he : HEq e f) {x y : D}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f φ) := by
  cases h
  cases he
  rfl

/-- 概要：任意の降順番号付けの立方体評価は標準の降順番号付けの評価と一致する。
方針：降順番号付けの一意性と濃度の等式で比較する。
規約：異なる Fin の表示は異種等号で扱う。
使われ方：Kerodon 2.5.9（Tag 00SC） の削除面の評価を標準成分へ移す。 -/
lemma cubeEvaluation_strictAnti_heq {A : Type u} [LinearOrder A] {S : Finset A} {m : ℕ}
    (e : Fin m ≃ S) (he : StrictAnti e) {x y : D}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) φ) := by
  have hc : S.card = m := by simpa using (Fintype.card_congr e).symm
  have hn : e = Fin.revPerm.trans (S.orderIsoOfFin hc).toEquiv := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.strictAnti_enumeration_unique
    · exact he
    · exact (S.orderIsoOfFin hc).strictMono.comp_strictAnti Fin.rev_strictAnti
  have hEnum : HEq e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) :=
    (heq_of_eq hn).trans (descendingEnumeration_heq_of_card S hc).symm
  exact cubeEvaluation_heq_of_enumeration hc.symm e _ hEnum φ

variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：coherent 単体の有限内部点の成分を指定した等しい次数で取り出す。
方針：指定次数が内部点数の負に等しいという証明を消去し、標準成分を返す。
規約：引数 k とその等式の証明によって次数の cast を隠す。
使われ方：HA 1.3.1.16 の dg 単体の hom フィールドと方程式の成分。 -/
def coherentCubeComponentAt
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (k : ℤ) (hk : k = -(S.card : ℤ)) :
    GradedHom R (s.obj (.mk a)) (s.obj (.mk b)) k := by
  subst hk
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab S

/-- 概要：次数を指定した成分は元の標準成分と異種等号で一致する。
方針：次数の等式を消去して定義を評価する。
規約：成分の値と向きを変えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の固定した次数での評価の比較。 -/
lemma coherentCubeComponentAt_heq
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (k : ℤ) (hk : k = -(S.card : ℤ)) :
    HEq (coherentCubeComponentAt s hab S k hk) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab S) := by
  subst hk
  rfl

/-- 概要：降順の立方体評価は同じ次数を指定した標準成分に等しい。
方針：降順評価の異種等号と次数を指定した成分の異種等号を合成する。
規約：両辺の次数は −m で固定する。
使われ方：HA 1.3.1.16 の境界公式の各成分を等号へ直す。 -/
lemma cubeEvaluation_coherent_eq_componentAt
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ} (e : Fin m ≃ S)
    (he : StrictAnti e) (hk : -(m : ℤ) = -(S.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S) = coherentCubeComponentAt s hab S (-(m : ℤ)) hk := by
  exact eq_of_heq ((cubeEvaluation_strictAnti_heq e he _).trans
    (coherentCubeComponentAt_heq s hab S _ hk).symm)

/-- 概要：合成面の通常順合成を指定した等しい終次数で取り出す。
方針：左右の内部点数の和が切断点を除いた点数であることを使う。
規約：後半の標準成分が後の射、前半の標準成分が前の射。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 方程式の合成項の同じ次数での表示。 -/
def coherentCubeCompositionAt
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (_hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) (k : ℤ) (hk : k = 1 - (S.card : ℤ)) :
    GradedHom R (s.obj (.mk a)) (s.obj (.mk b)) k :=
  compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) (by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_pathSplitCoordinates S j
      have hE := Finset.card_erase_add_one j.property
      omega)

private lemma compose_heq_degree {x y z : D} {p q k l : ℤ}
    (g : GradedHom R y z q) (f : GradedHom R x y p) (hk : p + q = k) (hl : p + q = l) :
    HEq (compose R g f hk) (compose R g f hl) := by
  have h : k = l := hk.symm.trans hl
  cases h
  rfl

/-- 概要：終次数を指定した合成面の合成は左右の標準成分の合成と異種等号で一致する。
方針：通常順合成の終次数の二つの等式を比較する。
規約：左右の各成分の次数は元のまま保つ。
使われ方：HA 1.3.1.16 の1面の評価の異種等号を同じ次数の等号へ直す。 -/
lemma coherentCubeCompositionAt_heq
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) (k : ℤ) (hk : k = 1 - (S.card : ℤ)) :
    HEq (coherentCubeCompositionAt s hab S j k hk)
      (compose R
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val))
        (show -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val).card : ℤ) +
          -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b).card : ℤ) =
          -(((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b).card + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val).card : ℕ) : ℤ)
            by push_cast; omega)) := by
  exact compose_heq_degree _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
