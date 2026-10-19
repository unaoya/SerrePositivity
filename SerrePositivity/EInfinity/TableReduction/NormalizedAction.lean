module

public import SerrePositivity.EInfinity.TableReduction.NormalizedMap
public import SerrePositivity.EInfinity.BarrattEccles.NormalizedNaturality

/-!
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

namespace SerrePositivity.EInfinity.TableReduction

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：実際の正規化鎖上で TR は右作用を値の逆置換へ送る（BF §1.3.6）。
方針：両辺の線形写像を正規化生成元で比較し、onSequence の同変性を使う。
規約：右乗法と左ラベル置換の逆元の関係を明示する。
使われ方：全射語の部分合成の対称群同変性の移送公式。 -/
@[simp] lemma normalizedMap_rightAction (n d : ℕ) (ρ : Equiv.Perm (Fin n))
    (x : (BarrattEccles.normalizedChains A n).X d) :
    normalizedMap A n d
      ((BarrattEccles.normalizedChainMap A (BarrattEccles.rightAction n ρ)).f d x) =
      Surjection.renameLinear A ρ⁻¹ (normalizedMap A n d x) := by
  let F := (normalizedMap A n d).comp
    ((BarrattEccles.normalizedChainMap A (BarrattEccles.rightAction n ρ)).f d).hom
  let G := (Surjection.renameLinear A ρ⁻¹).comp (normalizedMap A n d)
  have he : ModuleCat.ofHom F = ModuleCat.ofHom G := by
    apply BarrattEccles.normalizedGenerator_hom_ext A n d
    intro sx
    change normalizedMap A n d
      ((BarrattEccles.normalizedChainMap A (BarrattEccles.rightAction n ρ)).f d
        (BarrattEccles.normalizedGenerator A n d sx)) =
      Surjection.renameLinear A ρ⁻¹
        (normalizedMap A n d (BarrattEccles.normalizedGenerator A n d sx))
    rw [BarrattEccles.normalizedChainMap_generator, normalizedMap_generator,
      normalizedMap_generator]
    have heq : BarrattEccles.simplexEquiv n d ((BarrattEccles.rightAction n ρ).app _ sx) =
        fun j => BarrattEccles.simplexEquiv n d sx j * ρ := by
      funext j
      exact BarrattEccles.simplexEquiv_rightAction n d ρ sx j
    rw [heq]
    have h := onSequence_action A (BarrattEccles.simplexEquiv n d sx) ρ⁻¹
    simpa only [inv_inv] using h
  exact congrArg (fun f => f.hom x) he

end SerrePositivity.EInfinity.TableReduction
