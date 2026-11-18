module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Chains

/-!
模型。文献の定義との比較は後で
# 一般の table reduction 鎖写像

概要：Berger–Fresse §1.3.1・§1.4.4 の TR を実際の E(n) から χ(n) への鎖写像にする。
方針：全 arity の線形微分保存を隣接微分の可換性へ移す。
規約：鎖写像の全次数成分は既存の正規化 TR。
使われ方：χ のオペラッド構造と TR の部分合成保存の証明へ進む。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

/-- 概要：実際の Barratt–Eccles 鎖から全射語鎖への TR 鎖写像（BF §1.4.4）。
方針：全生成元の相殺から得た微分保存を ChainComplex.ofHom へ渡す。
規約：任意の可換環、零を含む全 arity、全非負次数。
使われ方：TR のオペラッド射性のうち鎖写像の条件を供給する。 -/
def chainMap (A : Type u) [CommRing A] (n : ℕ) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A n :=
  ChainComplex.ofHom (fun d => ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d)) (fun d => by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains_d]
    apply ModuleCat.hom_ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm A n d)

/-- 概要：TR 鎖写像の次数成分は元の正規化線形写像（BF §1.3.1）。
方針：構成の次数成分をそのまま評価する。
規約：基底と符号の規約を変更しない。
使われ方：生成元公式と部分合成の既存計算を鎖写像へ再利用する。 -/
@[simp] lemma chainMap_f (A : Type u) [CommRing A] (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap A n).f d = ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d) := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
