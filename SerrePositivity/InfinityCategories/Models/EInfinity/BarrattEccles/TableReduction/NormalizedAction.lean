module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NormalizedMap
public import SerrePositivity.EInfinity.BarrattEccles.NormalizedNaturality

/-!
模型。文献の定義との比較は後で
# 正規化 TR の実際の鎖上の置換同変性

概要：Berger–Fresse §1.3.6 の TR の対称群同変性を全正規化鎖上で評価する。
方針：正規化生成元で置換列の既存の同変性を使い、線形外延性で延長する。
規約：BE の右作用 ρ は全射語の値の左作用 ρ⁻¹ へ送られる。
使われ方：χ の部分合成の内外同変性を全射 TR から移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：実際の正規化鎖上で TR は右作用を値の逆置換へ送る（BF §1.3.6）。
方針：両辺の線形写像を正規化生成元で比較し、onSequence の同変性を使う。
規約：右乗法と左ラベル置換の逆元の関係を明示する。
使われ方：全射語の部分合成の対称群同変性の移送公式。 -/
@[simp] lemma normalizedMap_rightAction (n d : ℕ) (ρ : Equiv.Perm (Fin n))
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).X d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.rightAction n ρ)).f d x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A ρ⁻¹ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d x) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d).comp
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.rightAction n ρ)).f d).hom
  let G := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A ρ⁻¹).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d)
  have he : ModuleCat.ofHom F = ModuleCat.ofHom G := by
    apply _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator_hom_ext A n d
    intro sx
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.rightAction n ρ)).f d
        (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n d sx)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A ρ⁻¹
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n d sx))
    rw [_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainMap_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator]
    have heq : _root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d ((_root_.SerrePositivity.EInfinity.BarrattEccles.rightAction n ρ).app _ sx) =
        fun j => _root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d sx j * ρ := by
      funext j
      exact _root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv_rightAction n d ρ sx j
    rw [heq]
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_action A (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d sx) ρ⁻¹
    simpa only [inv_inv] using h
  exact congrArg (fun f => f.hom x) he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
