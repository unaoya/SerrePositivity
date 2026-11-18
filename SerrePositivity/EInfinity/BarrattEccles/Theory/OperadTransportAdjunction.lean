module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraTransport
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorAdjunctionMate

/-!
# 強モノイダル随伴によるオペラッド代数の移送

## 概要
Berger–Moerdijk 命題 4.1 のセル付加に使う、次数付き台への移送の随伴。

## 方針
arity 比較を互いの随伴像として与え、台の随伴を作用と両立する射に制限する。

## 規約
右側は lax braided、左側の arity 比較は同型。

## 使われ方
微分を消したオペラッド代数の pushout と自由代数の比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T]
  {L : Complex S ⥤ Complex T} {R : Complex T ⥤ Complex S}
  [L.LaxBraided] [IsIso (ε L)] [∀ X Y, IsIso (μ L X Y)] [R.LaxBraided] (a : L ⊣ R)
  (ha : let _ : L.Monoidal := Functor.Monoidal.ofLaxMonoidal L; a.IsMonoidal)
  {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad S} {Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad T}
  (l : LaxComparison L Q P) (r : LaxComparison R P Q)
  [∀ n, IsIso (l.arity n)]

include ha

/-- The action equation is preserved under the mate correspondence. -/
lemma transportAlgebraHom_mate
    (h : ∀ n, (a.homEquiv (P.arity n) (Q.arity n)).symm (r.arity n) =
      (asIso (l.arity n)).inv)
    (X : P.Algebra) (Y : Q.Algebra) (g : L.obj X.carrier ⟶ Y.carrier) (n : ℕ) :
    let g' := (a.homEquiv X.carrier Y.carrier) g
    (((transport l).obj X).action n ≫ g =
      (𝟙 (Q.arity n) ⊗ₘ TensorPowers.map g n) ≫ Y.action n) ↔
    (X.action n ≫ g' =
      (𝟙 (P.arity n) ⊗ₘ TensorPowers.map g' n) ≫ ((transport r).obj Y).action n) := by
  let : L.Monoidal := Functor.Monoidal.ofLaxMonoidal L
  let := ha
  let K := X.carrier
  let U := Y.carrier
  let p := laxPowerComparison L K n
  let q := laxPowerComparison R U n
  let g' : K ⟶ R.obj U := (a.homEquiv K U) g
  let b := laxTensorComparison L (l.arity n) p
  have hpIso : IsIso p := laxPowerComparison_isIso L K n
  have hb : IsIso b := by
    let i := (asIso (l.arity n) ⊗ᵢ asIso p) ≪≫ Functor.Monoidal.μIso L (P.arity n) (power K n)
    exact i.isIso_hom
  let m := (a.homEquiv (power K n) (power U n)).symm (TensorPowers.map g' n ≫ q)
  have hp : p ≫ m = TensorPowers.map g n := laxPowerComparison_mate a g n
  change (b ≫ L.map (X.action n)) ≫ g =
      (𝟙 (Q.arity n) ⊗ₘ TensorPowers.map g n) ≫ Y.action n ↔
    X.action n ≫ g' = (𝟙 (P.arity n) ⊗ₘ TensorPowers.map g' n) ≫
      laxTensorComparison R (r.arity n) q ≫ R.map (Y.action n)
  have hr :
      (𝟙 (P.arity n) ⊗ₘ TensorPowers.map g' n) ≫ laxTensorComparison R (r.arity n) q =
        laxTensorComparison R (r.arity n) (TensorPowers.map g' n ≫ q) := by
    simp only [laxTensorComparison, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [reassoc_of% hr, ← (a.homEquiv (P.arity n ⊗ power K n) U).symm.injective.eq_iff,
    a.homEquiv_naturality_left_symm, a.homEquiv_naturality_right_symm,
    laxTensorComparison_mate a, Equiv.symm_apply_apply, h n, ← cancel_epi b]
  change (b ≫ L.map (X.action n)) ≫ g =
      (𝟙 (Q.arity n) ⊗ₘ TensorPowers.map g n) ≫ Y.action n ↔
    b ≫ L.map (X.action n) ≫ g =
      b ≫ δ L (P.arity n) (power K n) ≫ ((asIso (l.arity n)).inv ⊗ₘ m) ≫ Y.action n
  simp only [b, laxTensorComparison, Category.assoc]
  have he : l.arity n ≫ (asIso (l.arity n)).inv = 𝟙 _ :=
    (asIso (l.arity n)).hom_inv_id
  rw [Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc, he, hp]

/-- Adjunction on algebras induced by compatible arity comparisons. -/
def transportAdjunction
    (h : ∀ n, (a.homEquiv (P.arity n) (Q.arity n)).symm (r.arity n) =
      (asIso (l.arity n)).inv) :
    transport l ⊣ transport r :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun g := ⟨(a.homEquiv X.carrier Y.carrier) g.hom,
            fun n => (transportAlgebraHom_mate a ha l r h X Y g.hom n).mp (g.comm n)⟩
          invFun g := ⟨(a.homEquiv X.carrier Y.carrier).symm g.hom,
            fun n => (transportAlgebraHom_mate a ha l r h X Y _ n).mpr (by
              simpa only [Equiv.apply_symm_apply] using g.comm n)⟩
          left_inv g := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (Equiv.symm_apply_apply _ _)
          right_inv g := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm f g := by
        apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
        exact a.homEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
        exact a.homEquiv_naturality_right f.hom g.hom }

end SerrePositivity.EInfinity.Operad
