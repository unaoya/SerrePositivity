module

public import SerrePositivity.InfinityCategories.Core.Join

/-!
概要：左因子が一頂点である join の単体の検出。
方針：始点への制限から左因子を復元し、右因子を保つ joinMap の像と合わせる。
規約：切断位置一は、最初の頂点だけが左因子に属することを表す。
使われ方：Kerodon Proposition 5.2.3.15、相対 join の外ホーンの充填の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子を保つ joinMap の像と左因子は join の単体を決定する。
方針：依存和の切断を像から読み、右因子に対する恒等作用を取り除く。
規約：左因子の一致は切断に沿う HEq で述べる。
使われ方：Kerodon Proposition 5.2.3.15、相対 join の持ち上げの一意性。 -/
lemma Join.Simplex.ext_of_joinMap_right_id {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (s t : Join.Simplex X Y n) (hx : HEq s.2.1 t.2.1)
    (hf : (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s =
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) t) : s = t := by
  rcases s with ⟨l, x, y⟩
  rcases t with ⟨k, x', y'⟩
  have hc : l = k := congrArg Sigma.fst hf
  cases hc
  have hx' : x = x' := eq_of_heq hx
  have hy : y = y' := by
    have he := Sigma.mk.inj_iff.mp hf
    have he' := eq_of_heq he.2
    simpa only [joinMap, Join.augHom_id] using congrArg Prod.snd he'
  cases hx'
  cases hy
  rfl

/-- 概要：切断一の単体では始点への制限が左因子をそのまま保つ。
方針：始点の逆像の切断は一で、左側の順序写像は恒等写像となる。
規約：始点への制限を Fin 1 からの定値順序写像で表す。
使われ方：Kerodon Proposition 5.2.3.15、外ホーンの始点からの左因子の復元。 -/
lemma Join.simplexMap_initial_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y n) (hs : s.1.val = 1) :
    HEq (Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) s).2.1
      s.2.1 := by
  let α := OrderHom.const (Fin 1) (0 : Fin (n + 1))
  have hc : Join.pullCut α s.1.val = s.1.val := by
    apply Join.cut_ext (Join.pullCut_le _ _) (by omega)
    intro i
    rw [Join.lt_pullCut_iff]
    change 0 < s.1.val ↔ i.val < s.1.val
    have := i.isLt
    omega
  have he := Join.augMap_congr X hc rfl (Join.leftMap α s.1.val) OrderHom.id
    (fun i j hij ↦ by
      change 0 = j.val
      have := j.isLt
      omega) s.2.1 s.2.1 rfl
  rw [Join.augMap_id] at he
  exact (cast_heq _ _).symm.trans (heq_of_eq he)

/-- 概要：切断一の join の単体は始点と、右因子を保つ joinMap の像から決まる。
方針：始点の一致から左因子の HEq を得て joinMap による検出を適用する。
規約：両単体は同じ次数で、左因子の射に単射性は仮定しない。
使われ方：Kerodon Proposition 5.2.3.15、標準 prism の垂直辺に沿う外ホーンの比較。 -/
lemma Join.Simplex.ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (s t : Join.Simplex X Y n)
    (hs : s.1.val = 1) (ht : t.1.val = 1)
    (h0 : Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) s =
      Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) t)
    (hf : (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s =
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) t) : s = t := by
  apply Join.Simplex.ext_of_joinMap_right_id f s t _ hf
  have hh : HEq
      (Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) s).2.1
      (Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) t).2.1 := by
    rw [h0]
  exact (Join.simplexMap_initial_left_heq s hs).symm.trans
    (hh.trans (Join.simplexMap_initial_left_heq t ht))

/-- 概要：切断一の像の単体は左因子の頂点の持ち上げから復元できる。
方針：右因子をそのまま使い、左因子の次数を切断の等式で移送する。
規約：左因子の像との整合性を HEq で指定する。
使われ方：Kerodon Proposition 5.2.3.15、係数側の充填単体から相対 join の充填を構成する。 -/
lemma Join.Simplex.exists_preimage_cut_one {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : Join.Simplex X' Y n) (ht : t.1.val = 1)
    (x : X _⦋0⦌) (hx : HEq (f.app (Opposite.op ⦋0⦌) x) t.2.1) :
    ∃ s : Join.Simplex X Y n, s.1.val = 1 ∧ HEq s.2.1 x ∧
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s = t := by
  let z : Join.augObj X t.1.val := cast (congrArg (Join.augObj X) ht.symm) x
  let s : Join.Simplex X Y n := ⟨t.1, z, t.2.2⟩
  refine ⟨s, ht, cast_heq _ _, ?_⟩
  refine Join.Simplex.ext ((joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s) t (by rfl) ?_ ?_
  · change Join.augHom f t.1.val z = t.2.1
    have he := Join.augHom_cast f ht.symm x
    exact he.symm.trans (eq_of_heq ((cast_heq _ _).trans hx))
  · exact Join.augHom_id Y _ _

end SerrePositivity.InfinityCategories
