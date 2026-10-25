module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTargetHom

/-!
概要：標的だけの MC 変形に対する加群 Hom の微分と、元の始域からの斉次合成を比較する。
方針：各評価の標的変形の微分式を主 Hom end へ戻す。
規約：元の全次数 Hom を使い、閉性を仮定する版は別名で供給する。
使われ方：bar の末端 HA 方程式を実 MC 摂動後の方程式へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (N : RightModule R D) (ψ : (moduleHom R D N N).X 1)
  (hψ : (moduleHom R D N N).d 1 2 ψ +
    compose R (x := N) (y := N) (z := N) ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def moduleMaurerCartanTargetDifferential (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) : (moduleHom R D M N).X (q + 1) :=
  let A : (moduleHom R D M N).X (q + 1) := (moduleHom R D M N).d q (q + 1) z
  let B : (moduleHom R D M N).X (q + 1) := compose R (x := M) (y := N) (z := N) ψ z rfl
  A + B

lemma moduleMaurerCartanTargetForget_d_rebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    moduleMaurerCartanTargetForget R D N ψ hψ M (q + 1)
      ((moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
        (moduleMaurerCartanTargetRebase R D N ψ hψ M q z)) =
      moduleMaurerCartanTargetDifferential R D N ψ M q z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetForget_π, moduleHomElement_d_π,
    moduleMaurerCartanTargetRebase_π]
  unfold moduleMaurerCartanTargetDifferential
  rw [map_add, moduleHomElement_d_π, moduleHomCompose_π]
  exact maurerCartanTargetHom_δ ((moduleHomπ R D N N x).f 1 ψ)
    (moduleMaurerCartan_evaluation R D N ψ hψ x) q ((moduleHomπ R D M N x).f q z)

lemma moduleMaurerCartanTargetRebase_d (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1)
      (moduleMaurerCartanTargetDifferential R D N ψ M q z) := by
  have h := congrArg (moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1))
    (moduleMaurerCartanTargetForget_d_rebase R D N ψ hψ M q z)
  simpa only [moduleMaurerCartanTargetRebase_forget] using h

lemma moduleMaurerCartanTargetRebase_d_of_closed (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) (hz : (moduleHom R D M N).d q (q + 1) z = 0) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1)
      (compose R (x := M) (y := N) (z := N) ψ z rfl) := by
  rw [moduleMaurerCartanTargetRebase_d, moduleMaurerCartanTargetDifferential, hz, zero_add]

lemma moduleMaurerCartanTargetRebase_comp (L M : RightModule R D) {p q n : ℤ}
    (f : (moduleHom R D L M).X p) (g : (moduleHom R D M N).X q) (hn : p + q = n) :
    moduleMaurerCartanTargetRebase R D N ψ hψ L n
      (compose R (x := L) (y := M) (z := N) g f hn) =
    compose R (x := L) (y := M) (z := moduleMaurerCartan R D N ψ hψ)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q g) f hn := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetRebase_π, moduleHomCompose_π,
    moduleHomCompose_π, moduleMaurerCartanTargetRebase_π]
  apply Cochain.ext
  intro i j hij
  simp only [maurerCartanTargetRebaseCochain, Cochain.mk_v]
  rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
  rfl

end SerrePositivity.DifferentialGraded
