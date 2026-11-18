module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ZeroAugmentation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CochainDegrees
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegreeZero
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationCochainValues

/-!
模型。文献の定義との比較は後で
# 零次の TR と BE augmentation の整合性

概要：Berger–Fresse §1.3・§3.1 の区間端点条件に必要な実際の係数比較を証明する。
方針：次数零の TR を一行または空語で評価し、生成元から線形に延長する。
規約：全 arity・任意の可換環、χ のオペラッド augmentation は使わない。
使われ方：区間の端点・収縮を BE augmentation に対する余代数射にする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全 arity の零次 TR の係数 augmentation 値は一（BF §1.3）。
方針：正 arity は一行の逆置換、零 arity は空語の生成元を評価する。
規約：元の BE の零単体は任意。
使われ方：TR の零次と BE augmentation の線形比較の基底計算。 -/
lemma zeroAugmentation_normalizedMap_generator (n : ℕ)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n 0 (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n 0 x)) = 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator]
  cases n with
  | zero => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation_empty]
  | succ n =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_degree_zero A (Nat.zero_lt_succ n)]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation_generator A _ (Equiv.surjective _)

/-- 概要：零次の正規化 TR の後の係数和は BE の鎖 augmentation（BF §1.3・§3.1）。
方針：両線形写像を全ての零単体生成元で比較する。
規約：実際の正規化鎖の零成分、全 arity。
使われ方：任意の係数の元で端点・収縮条件を検証する。 -/
lemma zeroAugmentation_normalizedMap (n : ℕ) :
    ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n 0) ≫
      ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n) =
        (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainContraction A n).hom.f 0 := by
  apply _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator_hom_ext A n 0
  intro x
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n 0 (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n 0 x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.zeroAugmentation_normalizedMap_generator]
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedAugmentation_generator_zero A n x).symm

/-- 概要：整数零次の TR の係数和は実際の BE augmentation の値（BF §1.3・§3.1）。
方針：非正成分の比較公式と鎖の係数比較を整数模型へ移す。
規約：任意の整数零次の入力元、全 arity。
使われ方：E-coalgebra 区間の端点・収縮の零次条件。 -/
lemma zeroAugmentation_cochainMap_zero (n : ℕ) (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).hom ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n).f 0 x)) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_nonpos_hom_apply A n 0 (by omega) x
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).hom ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n).f 0 x) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n 0 ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexXIso A n 0).hom x) at ht
  rw [ht]
  have h := congrArg (fun f => f ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexXIso A n 0).hom x))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.zeroAugmentation_normalizedMap A n)
  refine h.trans ?_
  have h' := _root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation_zero_apply A n
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexXIso A n 0).hom x)
  simpa only [ModuleCat.inv_hom_apply] using! h'.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
