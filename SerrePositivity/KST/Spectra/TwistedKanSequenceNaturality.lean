module

public import SerrePositivity.KST.Spectra.TwistedKanSequence

/-!
概要：自己射の反復による構造変更の比較は可換する射に対して自然。
方針：各段で可換式を反復回数について帰納する。
規約：対合性や Ω 条件は不要。
使われ方：BF 1978 §2、HA §1.4.2。loop 模型の符号補正の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自己射と可換する射はその任意回数の反復とも可換する。
方針：反復の帰納的定義と合成の結合則を使う。
規約：段と反復回数は独立。
使われ方：BF 1978 §2。符号反転の段ごとの反復。 -/
theorem iterateHom_natural {X Y : KanSequence.{u}} (r : Hom X X) (s : Hom Y Y)
    (f : Hom X Y) (h : ∀ k, r.app k ≫ f.app k = f.app k ≫ s.app k) (m k : ℕ) :
    (iterateHom r m).app k ≫ f.app k = f.app k ≫ (iterateHom s m).app k := by
  induction m with
  | zero => simp only [iterateHom, Category.id_comp, Category.comp_id]
  | succ m ih =>
    change ((iterateHom r m).app k ≫ r.app k) ≫ f.app k =
      f.app k ≫ ((iterateHom s m).app k ≫ s.app k)
    rw [Category.assoc, h k, ← Category.assoc, ih, Category.assoc]

/-- 概要：構造変更の比較は可換する射に対して各段で厳密に自然。
方針：n 段の比較は自己射の n 回反復であることを使う。
規約：構造を変える前後の段の対象は同一。
使われ方：BF 1978 §2、HA §1.4.2。有理化の単位の符号補正。 -/
theorem twistMap_natural_app {X Y : KanSequence.{u}} (r : Hom X X) (s : Hom Y Y)
    (f : Hom X Y) (h : ∀ k, r.app k ≫ f.app k = f.app k ≫ s.app k) (n : ℕ) :
    (twistMap r).app n ≫ f.app n = f.app n ≫ (twistMap s).app n :=
  iterateHom_natural r s f h n n

end SerrePositivity.KST.Spectra.KanSequence
