module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDescComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayer

/-!
概要：切断代数への任意の底射の零降下は、元の代数射の自然性を厳密に保つ。
方針：遷移自然性を使い、零切断への降下の後合成則を適用する。
規約：元の底射と代数射を保持。使われ方：右係数標的の標準制限との同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [P.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C)

local instance zeroDesc_source_lowerBound : (postnikov R B 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R B 0
local instance zeroDesc_target_lowerBound : (postnikov R C 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R C 0

lemma postnikovZeroDesc_map :
    postnikovDesc R 0 ((b ≫ postnikovMap R f n) ≫ postnikovTransition R C n 0 hn) =
      postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn) ≫ postnikovMap R f 0 := by
  have h : (b ≫ postnikovMap R f n) ≫ postnikovTransition R C n 0 hn =
      (b ≫ postnikovTransition R B n 0 hn) ≫ postnikovMap R f 0 := by
    rw [Category.assoc, postnikovTransition_naturality, ← Category.assoc]
  exact (congrArg (fun t => postnikovDesc R 0 t) h).trans
    (postnikovDesc_postcompose R 0 _ _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
