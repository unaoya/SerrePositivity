module

public import SerrePositivity.EInfinity.Operad.Basic

/-!
# arity の移送と対称列の全単射の作用

概要：Berger–Moerdijk §1 の外側等変性で、等しい長さの異なる式の間の対称列の作用を比較する。
方針：始域と終域の arity の等式で同一視し、Fin の全単射の移送を簡約する。
規約：同じ長さの置換から、異なる長さの式で表した標準有限集合間の全単射を得る。
使われ方：二入力の外側交換の出力をブロック交換の全単射として記述する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：置換作用の前後の arity の移送は一つの全単射の作用にまとめられる（Berger–Moerdijk §1）。
方針：始域と終域の等式で長さを同一視して移送を簡約する。
規約：置換を始域から戻して終域へ移す向きで全単射を合成する。
使われ方：外側等変性で得た出力の置換を、二ブロックの交換の全単射へ直す。 -/
lemma arity_map_permutation_transport (P : Operad A) {r s t : ℕ}
    (h : r = s) (k : r = t) (σ : Equiv.Perm (Fin r)) :
    P.sequence.map (FiniteBijection.permutation r σ) ≫ eqToHom (congrArg P.arity k) =
      eqToHom (congrArg P.arity h) ≫ P.sequence.map
        (FiniteBijection.homOfEquiv (X := FiniteBijection.of s) (Y := FiniteBijection.of t)
          ((finCongr h).symm.trans (σ.trans (finCongr k)))) := by
  subst s
  subst t
  have he : ((finCongr (Eq.refl r)).symm.trans (σ.trans (finCongr (Eq.refl r)))) = σ := by
    ext i
    rfl
  simp only [he, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.Operad
