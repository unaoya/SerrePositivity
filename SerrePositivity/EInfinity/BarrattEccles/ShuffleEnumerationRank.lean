module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePermutationCharacterization

/-!
# 昇順列挙の添字と接頭辺数

概要：Berger–Fresse §1.1.3 の辺の位置と shuffle 置換の入力位置を対応づける。
方針：昇順列挙で指定された辺より前の辺と、添字より前の有限順序との全単射を数える。
規約：添字は 0 始まりで、その値は厳密に前にある辺数である。
使われ方：置換の削除の signature の公式を経路の座標で表す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：昇順列挙での添字はその値より小さい集合の要素の個数である（Berger–Fresse §1.1.3）。
方針：添字の初期区間と集合内の初期区間を昇順同値で全単射にする。
規約：有限順序の部分集合で述べ、添字の濃度は k とする。
使われ方：shuffle 置換の逆像の番号を経路座標の接頭辺数で計算する。 -/
lemma orderIsoOfFin_index {N k : ℕ} (s : Finset (Fin N)) (hs : s.card = k) (a : s) :
    ((s.orderIsoOfFin hs).symm a).val = (s.filter (fun x => x < a.val)).card := by
  let e := s.orderIsoOfFin hs
  have h : (Finset.Iio (e.symm a)).card = (s.filter (fun x => x < a.val)).card := by
    apply Finset.card_bij (fun j _ => (e j).val)
    · intro j hj
      have hlt : e j < a := by
        simpa only [e.apply_symm_apply] using e.strictMono (Finset.mem_Iio.mp hj)
      exact Finset.mem_filter.mpr ⟨(e j).property, hlt⟩
    · intro j _ l _ hjl
      exact e.injective (Subtype.ext hjl)
    · intro x hx
      let b : s := ⟨x, (Finset.mem_filter.mp hx).1⟩
      have hb : b < a := (Finset.mem_filter.mp hx).2
      refine ⟨e.symm b, Finset.mem_Iio.mpr (e.symm.strictMono hb), ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply b)
  simpa only [Fin.card_Iio] using h

/-- 概要：水平辺の shuffle 置換による逆像は水平座標に等しい（Berger–Fresse §1.1.3）。
方針：水平辺の昇順列挙を逆に適用し、その添字を接頭辺数で計算する。
規約：位置 a 自身を含めず、その直前の頂点の水平座標を使う。
使われ方：水平辺の削除の signature の変化を求める。 -/
lemma ShufflePath.permutation_symm_val_of_mem {p q : ℕ} (s : ShufflePath p q)
    (a : Fin (p + q)) (ha : a ∈ s.val) :
    (s.permutation.symm a).val = (s.horizontal a.castSucc).val := by
  let e := s.val.orderIsoOfFin s.property
  have hj : s.permutation.symm a = Fin.castAdd q (e.symm ⟨a, ha⟩) := by
    apply s.permutation.injective
    rw [s.permutation.apply_symm_apply, s.permutation_castAdd]
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)).symm
  rw [hj]
  change (e.symm ⟨a, ha⟩).val = (s.val.filter (fun x => x.val < a.val)).card
  exact orderIsoOfFin_index s.val s.property ⟨a, ha⟩

/-- 概要：垂直辺の shuffle 置換による逆像は p と垂直座標の和である（Berger–Fresse §1.1.3）。
方針：第二ブロックの昇順列挙の添字を接頭垂直辺数で計算する。
規約：第二ブロックは p から始まるため p を加える。
使われ方：垂直辺の削除に伴う Koszul 符号を計算する。 -/
lemma ShufflePath.permutation_symm_val_of_notMem {p q : ℕ} (s : ShufflePath p q)
    (a : Fin (p + q)) (ha : a ∉ s.val) :
    (s.permutation.symm a).val = p + (s.vertical a.castSucc).val := by
  let e := s.valᶜ.orderIsoOfFin s.compl_card
  let b : {x // x ∈ s.valᶜ} := ⟨a, Finset.mem_compl.mpr ha⟩
  have hj : s.permutation.symm a = Fin.natAdd p (e.symm b) := by
    apply s.permutation.injective
    rw [s.permutation.apply_symm_apply, s.permutation_natAdd]
    exact (congrArg Subtype.val (e.apply_symm_apply b)).symm
  rw [hj]
  change p + (e.symm b).val = p + (s.valᶜ.filter (fun x => x.val < a.val)).card
  rw [show (e.symm b).val = (s.valᶜ.filter (fun x => x.val < a.val)).card from
    orderIsoOfFin_index s.valᶜ s.compl_card b]

end SerrePositivity.EInfinity.BarrattEccles
