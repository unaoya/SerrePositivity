module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
模型。文献の定義との比較は後で
# 符号付き削除による次数を下げる線形写像

概要：Berger–Fresse §1.2.3 の削除の和を次数 d+1 から d への線形写像にする。
方針：各基底語で符号付き削除を足し、自由加群の普遍性で延長する。
規約：d²=0 はここでは主張せず、TR との両立から後で証明する。
使われ方：一般の table reduction の微分保存を述べる値域の微分となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：基底語の符号付き削除の和（BF §1.2.3）。
方針：各文字を除き、退化・非全射項を零として整数係数で足す。
規約：次数 d+1 から d へ移す。
使われ方：自由加群への線形延長の生成元上の値を指定する。 -/
def differentialOnWord {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  ∑ i : Fin (n + (d + 1)), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val i • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val i)

/-- 概要：削除の和を次数成分の線形写像へ延長する（BF §1.2.3）。
方針：自由加群上の線形結合を使う。
規約：まだ ChainComplex の d_comp_d フィールドには束ねない。
使われ方：TR の鎖写像性と平方零の証明の対象となる。 -/
def differential (n d : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n (d + 1) →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  Finsupp.linearCombination A (fun v : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A v.down)

/-- 概要：削除の線形写像は指定した基底語の和を与える（BF §1.2.3）。
方針：一点の有限台関数に対する線形結合を評価する。
規約：整数係数は加法群への作用として扱う。
使われ方：線形写像の比較を語ごとに帰着する。 -/
@[simp]
lemma differential_basis {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n (d + 1) (ULift.up v)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A v := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis_apply]
  change Finsupp.linearCombination A _ (Finsupp.single _ 1) = _
  simp only [Finsupp.linearCombination_single, one_smul]

/-- 概要：基底語の削除の和は値の置換と両立する（BF §1.2.3）。
方針：削除・係数・正規化の置換との可換性を和の各項へ適用する。
規約：退化な削除項も零として含める。
使われ方：微分の Σ_n 同変性を線形に拡張する。 -/
lemma differentialOnWord_rename {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A v) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord, map_sum, map_zsmul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_generator]
  apply Finset.sum_congr rfl
  intro i _
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (σ ∘ v.val) i • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (σ ∘ v.val) i) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_rename, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_rename]

/-- 概要：次数を下げる線形写像は対称群作用と可換（BF §1.2.3）。
方針：両辺を自由基底で比較し、基底語の削除の同変性を使う。
規約：ここで構成するのは線形写像の等式で、平方零は未使用。
使われ方：χ の対称列の微分と TR の同変性を構成する。 -/
lemma differential_renameLinear (n d : ℕ) (σ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n (d + 1)).ext
  intro v
  obtain ⟨v⟩ := v
  simp only [LinearMap.comp_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_basis, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_basis]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord_rename A σ v

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
