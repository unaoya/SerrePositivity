module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadTensorComparison
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
# オペラッド代数の lax braided 関手に沿う移送

## 概要
Berger–Moerdijk §1 の代数を、作用の係数の比較射を使って移す。

## 方針
係数と入力テンソルの比較を作用の前に合成する。

## 規約
比較射に可逆性を仮定せず、零入力の演算を含める。

## 使われ方
M13 の係数拡大と係数制限に同じ移送を使う。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
open Functor.LaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T]
  {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad S} {Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad T} {F : Complex T ⥤ Complex S} [F.LaxBraided]

/-- lax braided 関手を介した arity ごとのオペラッドの比較。 -/
structure LaxComparison (F : Complex T ⥤ Complex S) [F.LaxBraided]
    (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad S) (Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad T) where
  arity (n : ℕ) : P.arity n ⟶ F.obj (Q.arity n)
  permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LaxComparisonSquare F (arity n) (arity n)
      (P.sequence.map (FiniteBijection.permutation n σ))
      (Q.sequence.map (FiniteBijection.permutation n σ))
  unit : LaxComparisonSquare F (ε F) (arity 1) P.unit Q.unit
  comp (m n : ℕ) (i : Fin (m + 1)) :
    LaxComparisonSquare F (laxTensorComparison F (arity (m + 1)) (arity n)) (arity (m + n))
      (P.comp m n i) (Q.comp m n i)

variable (k : LaxComparison F P Q)

/-- lax braided 関手に沿って移した代数の作用。 -/
def transportAction (X : Q.Algebra) (n : ℕ) :
    P.arity n ⊗ power (F.obj X.carrier) n ⟶
      F.obj X.carrier :=
  laxTensorComparison F (k.arity n)
    (laxPowerComparison F X.carrier n) ≫
      F.map (X.action n)

/-- 作用の移送は入力置換を保つ。 -/
lemma transportAction_equivariance (X : Q.Algebra) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction (F.obj X.carrier) n σ).asIso.hom) ≫
      transportAction k X n = transportAction k X n := by
  let c := k.arity n
  let p := laxPowerComparison F X.carrier n
  have hc : LaxComparisonSquare F c c
      (P.sequence.map (FiniteBijection.permutation n σ))
      (Q.sequence.map (FiniteBijection.permutation n σ)) := k.permutation n σ
  have h := LaxComparisonSquare.tensor F hc (laxPowerComparison_permutation F X.carrier n σ)
  unfold LaxComparisonSquare at h
  change _ ≫ laxTensorComparison F c p ≫ F.map (X.action n) =
    laxTensorComparison F c p ≫ F.map (X.action n)
  rw [reassoc_of% h, ← F.map_comp, X.equivariance]

/-- 作用の移送は単位演算を保つ。 -/
lemma transportAction_unit (X : Q.Algebra) :
    (P.unit ▷ power (F.obj X.carrier) 1) ≫
        transportAction k X 1 =
      (λ_ (power (F.obj X.carrier) 1)).hom ≫
        (oneIso (F.obj X.carrier)).hom := by
  let c := k.arity 1
  let p := laxPowerComparison F X.carrier 1
  let K := power X.carrier 1
  have hUnit : LaxComparisonSquare F (ε F) c P.unit Q.unit :=
    k.unit
  have h := LaxComparisonSquare.whiskerRight F p hUnit
  unfold LaxComparisonSquare at h
  change _ ≫ laxTensorComparison F c p ≫ F.map (X.action 1) = _
  rw [reassoc_of% h, ← F.map_comp, X.unit_action, F.map_comp]
  have he : laxTensorComparison F (ε F) p ≫ F.map (λ_ K).hom =
      (λ_ (power (F.obj X.carrier) 1)).hom ≫ p := by
    simp only [laxTensorComparison, tensorHom_def', Category.assoc]
    rw [← left_unitality, leftUnitor_naturality]
  rw [reassoc_of% he, laxPowerComparison_one]

/-- 作用の移送は部分合成を保つ。 -/
lemma transportAction_comp (X : Q.Algebra) (m n : ℕ)
    (i : Fin (m + 1)) :
    (P.comp m n i ▷ power (F.obj X.carrier) (m + n)) ≫
        transportAction k X (m + n) =
      (α_ (P.arity (m + 1)) (P.arity n)
        (power (F.obj X.carrier) (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction
        (F.obj X.carrier) (P.arity n) m n i
          (transportAction k X n)) ≫ transportAction k X (m + 1) := by
  let c := k.arity
  let p := laxPowerComparison F X.carrier
  have hComp : LaxComparisonSquare F (laxTensorComparison F (c (m + 1)) (c n)) (c (m + n))
      (P.comp m n i) (Q.comp m n i) :=
    k.comp m n i
  have h₁ := LaxComparisonSquare.whiskerRight F (p (m + n)) hComp
  have h₂ := LaxComparisonSquare.comp F
    (LaxComparisonSquare.associator F (c (m + 1)) (c n) (p (m + n)))
    (LaxComparisonSquare.whiskerLeft F (c (m + 1))
      (laxPowerComparison_insertion F X.carrier (Q.arity n) (P.arity n)
        (c n) m n i (X.action n)))
  unfold LaxComparisonSquare at h₁ h₂
  change _ ≫ laxTensorComparison F (c (m + n)) (p (m + n)) ≫ F.map (X.action (m + n)) =
    _ ≫ _ ≫ laxTensorComparison F (c (m + 1)) (p (m + 1)) ≫ F.map (X.action (m + 1))
  rw [reassoc_of% h₁, ← F.map_comp, X.comp_action]
  have h := congrArg (fun a => a ≫ F.map (X.action (m + 1))) h₂
  simpa only [F.map_comp, Category.assoc, transportAction, c, p] using h.symm

/-- オペラッドの比較に沿って移した代数。 -/
def transportObj (X : Q.Algebra) : P.Algebra where
  carrier := F.obj X.carrier
  action := transportAction k X
  equivariance := transportAction_equivariance k X
  unit_action := transportAction_unit k X
  comp_action := transportAction_comp k X

/-- オペラッドの比較による代数圏の関手。 -/
def transport : Q.Algebra ⥤ P.Algebra where
  obj := transportObj k
  map {X Y} g := {
    hom := F.map g.hom
    comm n := by
      let c := k.arity n
      have hP : LaxComparisonSquare F (laxPowerComparison F X.carrier n)
          (laxPowerComparison F Y.carrier n) (TensorPowers.map (F.map g.hom) n)
          (TensorPowers.map g.hom n) := laxPowerComparison_naturality F g.hom n
      have h := LaxComparisonSquare.tensor F (LaxComparisonSquare.id F c) hP
      unfold LaxComparisonSquare at h
      change (laxTensorComparison F c (laxPowerComparison F X.carrier n) ≫ F.map (X.action n)) ≫
        F.map g.hom = _ ≫ laxTensorComparison F c (laxPowerComparison F Y.carrier n) ≫
          F.map (Y.action n)
      rw [Category.assoc, ← F.map_comp, g.comm]
      simp only [F.map_comp, reassoc_of% h] }
  map_id X := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact F.map_id X.carrier
  map_comp {_ _ _} g h := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact F.map_comp g.hom h.hom

end SerrePositivity.EInfinity.Operad
