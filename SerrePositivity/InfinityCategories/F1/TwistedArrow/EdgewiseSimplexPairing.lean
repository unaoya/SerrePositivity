module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOutsideSimplices

/-!
概要：edgewise の延長領域の外の非退化単体の pairing。
方針：有限頂点集合の挿入・削除の全単射を非退化単体へ移す。
規約：このファイルでは pairing のデータを構成し、正則性は別に証明する。
使われ方：Kerodon Corollary 8.1.1.13、右端射影の境界延長のホーン接合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：選んだ右頂点を含む領域外の非退化単体の集合。
方針：領域外の頂点集合への同値で型 I の条件を引き戻す。
規約：型 I はホーン接合で付け足す大きい方の単体。
使われ方：Kerodon Corollary 8.1.1.13、pairing の一方の型。 -/
noncomputable def edgewiseUpperSimplices (n : ℕ) : Set (edgewiseRightExtensionDomain.{u} n).N :=
  fun s ↦ edgewiseRightVertex n
    (edgewiseSupportPivot (edgewiseOutsideSimplexEquiv n s).val
      (edgewiseOutsideSimplexEquiv n s).property) ∈ (edgewiseOutsideSimplexEquiv n s).val

/-- 概要：選んだ右頂点を欠く領域外の非退化単体の集合。
方針：領域外の頂点集合への同値で型 II の条件を引き戻す。
規約：型 II は対の大きい単体の欠ける面。
使われ方：Kerodon Corollary 8.1.1.13、pairing のもう一方の型。 -/
noncomputable def edgewiseLowerSimplices (n : ℕ) : Set (edgewiseRightExtensionDomain.{u} n).N :=
  fun s ↦ edgewiseRightVertex n
    (edgewiseSupportPivot (edgewiseOutsideSimplexEquiv n s).val
      (edgewiseOutsideSimplexEquiv n s).property) ∉ (edgewiseOutsideSimplexEquiv n s).val

/-- 概要：型 I の非退化単体と大きい頂点集合の全単射。
方針：領域外の単体の全単射を右頂点の所属条件へ制限する。
規約：順方向は頂点集合の取り出し。
使われ方：Kerodon Corollary 8.1.1.13、有限集合の pairing の標的の移送。 -/
noncomputable def edgewiseUpperSimplexEquiv (n : ℕ) :
    {s // s ∈ edgewiseUpperSimplices.{u} n} ≃ EdgewiseUpperSupport n :=
  (edgewiseOutsideSimplexEquiv n).subtypeEquiv (fun _ ↦ Iff.rfl)

/-- 概要：型 II の非退化単体と小さい頂点集合の全単射。
方針：領域外の単体の全単射を右頂点の不在の条件へ制限する。
規約：順方向は頂点集合の取り出し。
使われ方：Kerodon Corollary 8.1.1.13、有限集合の pairing の始域の移送。 -/
noncomputable def edgewiseLowerSimplexEquiv (n : ℕ) :
    {s // s ∈ edgewiseLowerSimplices.{u} n} ≃ EdgewiseLowerSupport n :=
  (edgewiseOutsideSimplexEquiv n).subtypeEquiv (fun _ ↦ Iff.rfl)

/-- 概要：edgewise の延長領域の外の非退化単体の pairing。
方針：右頂点の有無で分割し、有限頂点集合の挿入の全単射を合成する。
規約：正則性や延長の存在をこの定義には含めない。
使われ方：Kerodon Corollary 8.1.1.13、全ての欠ける単体をホーンの対にまとめる。 -/
noncomputable def edgewiseExtensionPairing (n : ℕ) : (edgewiseRightExtensionDomain.{u} n).Pairing where
  I := edgewiseUpperSimplices n
  II := edgewiseLowerSimplices n
  inter := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
    change (_ ∧ ¬ _) ↔ False
    tauto
  union := by
    classical
    ext s
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change _ ∨ ¬ _
    exact Classical.em _
  p := (edgewiseLowerSimplexEquiv n).trans
    ((edgewiseSupportPairEquiv n).trans (edgewiseUpperSimplexEquiv n).symm)

/-- 概要：pairing の像の頂点集合は選んだ右頂点を一つ挿入したもの。
方針：上の型の全単射の往復の等式から頂点集合の値を取る。
規約：順方向の単体の型は II、大きい方は I。
使われ方：Kerodon Corollary 8.1.1.13、対の余次元一と順位の計算。 -/
lemma edgewiseExtensionPairing_support (n : ℕ) (s : (edgewiseExtensionPairing.{u} n).II) :
    stdSimplexNondegenerateSupport ((edgewiseExtensionPairing n).p s).val.toN =
      insert (edgewiseRightVertex n (edgewiseSupportPivot
        (stdSimplexNondegenerateSupport s.val.toN)
        (edgewiseOutsideSimplexEquiv n s.val).property))
        (stdSimplexNondegenerateSupport s.val.toN) := by
  have h := (edgewiseUpperSimplexEquiv n).apply_symm_apply
    ((edgewiseSupportPairEquiv n) (edgewiseLowerSimplexEquiv n s))
  exact congrArg (fun t : EdgewiseUpperSupport n ↦ t.val.val) h

end SerrePositivity.InfinityCategories
