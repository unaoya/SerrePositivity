module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransition
public import SerrePositivity.KST.ProExcision.Pro

/-!
概要：実 dg 代数の有限 Postnikov 切断を、自然数添字の逆系として構成する。
方針：元の代数遷移射の厳密な三則を既存 pro 最小形式へ渡す。
規約：ProExcision は読み取り専用。使われ方：有限切断の平方零比較と pro 零性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.KST.ProExcision
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]

def postnikovTower : Tower (Mon (Complex R)) where
  obj n := postnikov R B (n : ℤ)
  transition {m n} h := postnikovTransition R B m n (by omega)
  transition_self n := postnikovTransition_id R B n
  transition_comp hm hn := postnikovTransition_comp R B _ _ _ (by omega) (by omega)

def postnikovTowerMap {C : Mon (Complex R)} [C.X.IsStrictlyLE 0] (f : B ⟶ C) :
    LevelHom (postnikovTower R B) (postnikovTower R C) where
  app n := postnikovMap R f n
  naturality {_ _} h := (postnikovTransition_naturality R B f _ _ (by omega)).symm

lemma postnikovTower_quotient_transition {m n : ℕ} (h : n ≤ m) :
    postnikovQuotient R B m ≫ (postnikovTower R B).transition h =
      postnikovQuotient R B n := postnikovQuotient_transition R B m n (by omega)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
