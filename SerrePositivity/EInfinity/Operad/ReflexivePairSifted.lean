module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Reflexive coequalizer の添字圏の sifted 性

概要：Berger–Moerdijk §1 の代数の余極限に使う reflexive pair の形は sifted である。
方針：任意の二対象からの余錐を、共通切断を使った三辺の zigzag で標準余錐へ結ぶ。
規約：WalkingReflexivePair の zero は対の値域、one は始域。
使われ方：有限テンソル冪による reflexive coequalizer の保存を導く。
-/

@[expose] public section

namespace SerrePositivity.EInfinity

open CategoryTheory Limits
open WalkingReflexivePair

private def toZero : ∀ X : WalkingReflexivePair, X ⟶ zero
  | zero => 𝟙 zero
  | one => Hom.right

private def bridge : ∀ {X : WalkingReflexivePair}, (X ⟶ zero) → (X ⟶ one)
  | zero, .id _ => Hom.reflexion
  | one, .left => 𝟙 one
  | one, .right => Hom.rightCompReflexion

private lemma bridge_left {X : WalkingReflexivePair} (f : X ⟶ zero) :
    bridge f ≫ Hom.left = f := by cases f <;> rfl

private lemma bridge_right {X : WalkingReflexivePair} (f : X ⟶ zero) :
    bridge f ≫ Hom.right = toZero X := by cases f <;> rfl

private lemma diagonal_connected (X Y : WalkingReflexivePair) :
    IsConnected (StructuredArrow (X, Y) (Functor.diag WalkingReflexivePair)) := by
  let base : StructuredArrow (X, Y) (Functor.diag WalkingReflexivePair) :=
    StructuredArrow.mk (Y := zero) (toZero X, toZero Y)
  refine IsConnected.of_induct (j₀ := base) ?_
  intro p hp hm t
  let f := t.hom.1 ≫ toZero t.right
  let g := t.hom.2 ≫ toZero t.right
  let mid : StructuredArrow (X, Y) (Functor.diag WalkingReflexivePair) :=
    StructuredArrow.mk (Y := zero) (f, g)
  let high : StructuredArrow (X, Y) (Functor.diag WalkingReflexivePair) :=
    StructuredArrow.mk (Y := one) (bridge f, bridge g)
  let a : t ⟶ mid := StructuredArrow.homMk (toZero t.right) (by rfl)
  let b : high ⟶ mid := StructuredArrow.homMk Hom.left (by
    apply Prod.ext <;> dsimp [high, mid] <;> exact bridge_left _)
  let d : high ⟶ base := StructuredArrow.homMk Hom.right (by
    apply Prod.ext <;> dsimp [high, base] <;> exact bridge_right _)
  exact (hm a).2 ((hm b).1 ((hm d).2 hp))

/-- 概要：reflexive pair の添字圏は sifted（BM §1）。
方針：二対象から対角への structured arrow の連結性と非空性を検証する。
規約：共通切断の二つの関係を明示的な橋の構成で使う。
使われ方：代数の reflexive coequalizer の存在と忘却による保存を与える。 -/
instance walkingReflexivePair_isSifted : IsSifted WalkingReflexivePair := by
  have : Functor.Final (Functor.diag WalkingReflexivePair) :=
    ⟨fun ⟨X, Y⟩ => diagonal_connected X Y⟩
  exact ⟨⟩

end SerrePositivity.EInfinity
