module

public import SerrePositivity.EInfinity.IntervalCuts.Endpoints

/-!
# 正規化区間の収縮の全次数の値

概要：Berger–Fresse §3.1 の区間収縮を単位複体の実際の生成元で評価する。
方針：零次の比較同型を消去し、それ以外は single 複体の零性を使う。
規約：任意の可換環と全整数次数。
使われ方：収縮の具体的な鎖ホモトピーと余代数射性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：収縮は各頂点を単位複体の実際の一へ送る（BF §3.1）。
方針：零次の比較同型の逆を既存の頂点値へ適用する。
規約：比較後の値でなく実際の零次成分で述べる。
使われ方：収縮後に端点を施す鎖射の生成元計算。 -/
lemma contraction_vertex_eq (b : Fin 2) :
    (contraction A).f 0 (faceVector A (vertex b)) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  have H := congrArg (fun x => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv x)
    (contraction_vertex A b)
  simpa only [ModuleCat.inv_hom_apply] using! H

/-- 概要：収縮の零以外の次数の値は零（BF §3.1）。
方針：単位複体の零以外の成分の零性で射を零射に比較する。
規約：全整数次数、始域の元は任意。
使われ方：辺と他の次数での収縮・余作用保存を計算する。 -/
lemma contraction_eq_zero_of_ne_zero (r : ℤ) (hr : r ≠ 0) (x : (interval A).X r) :
    (contraction A).f r x = 0 := by
  have H : (contraction A).f r = 0 :=
    (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) r hr).eq_of_tgt _ _
  exact congrArg (fun f => f x) H

/-- 概要：収縮後の任意の端点は元の両頂点を同じ指定頂点へ送る（BF §3.1）。
方針：収縮の頂点値と端点の零次生成元公式を連結する。
規約：元の頂点と戻す端点は独立に指定できる。
使われ方：恒等射と端点への収縮のホモトピーの零次条件。 -/
lemma contraction_endpoint_vertex (b : Bool) (c : Fin 2) :
    (contraction A ≫ endpoint A b).f 0 (faceVector A (vertex c)) =
      faceVector A (vertex (if b then 1 else 0)) := by
  change (endpoint A b).f 0 ((contraction A).f 0 (faceVector A (vertex c))) = _
  rw [contraction_vertex_eq, endpoint_zero_apply, one_smul]

end SerrePositivity.EInfinity.IntervalCuts
