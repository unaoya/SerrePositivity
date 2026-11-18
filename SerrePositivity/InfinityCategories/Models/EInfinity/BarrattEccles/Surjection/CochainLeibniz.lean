module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CochainComposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainLeibniz

/-!
模型。文献の定義との比較は後で
# 全整数次数の全射語合成の微分条件

概要：Berger–Fresse §1.2.3–5 の χ の合成を整数コチェインの微分と両立させる。
方針：整数 TR の全次数の全射性で持ち上げ、合成保存と複体射の可換性で BE の法則を移す。
規約：整数の Koszul 符号を使い、正次数の零成分も含める。
使われ方：tensorLift に渡す部分合成の複体射の微分条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：χ の全整数次数の双線形合成はコチェインの Leibniz 則を満たす（BF §1.2.3–5）。
方針：整数 TR の二つの逆像で BE の全整数次数の法則を評価する。
規約：第二項の符号は第一の整数次数 r の negOnePow。
使われ方：加群テンソルの合成成分を複体射にする。 -/
lemma cochainCompositionBilinear_d (m n : ℕ) (i : Fin (m + 1)) (r s : ℤ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)).d (r + s) (r + s + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r s (r + s) rfl x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i (r + 1) s (r + s + 1) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).d r (r + 1) x) y +
      r.negOnePow • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r (s + 1) (r + s + 1) (by omega) x
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).d s (s + 1) y) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_f_surjective_int A (m + 1) r x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_f_surjective_int A n s y
  have h := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n)).f (r + s + 1) z)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.cochainShuffleBilinear_d A m n i r s x y)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_d_apply, map_add, Units.smul_def, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_compositionBilinear] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
