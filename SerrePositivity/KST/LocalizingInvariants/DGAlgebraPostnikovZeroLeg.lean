module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraZeroDescIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDescComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransitionHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActions
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology

/-!
概要：任意の有限 Postnikov 段へ入る元の脚を、零切断の元の脚へ自然に降ろす。
方針：元の切断遷移と降下の一意性を使い、準同型脚の可逆性も保つ。
規約：n=1 に制限しない。使われ方：高次有限段の共通零底と係数作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)
  {T U : Mon (Complex R)} [T.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0]
  (B C : NonpositiveAlgebra R)

local instance zeroLeg_B_lowerBound : (postnikov R B.obj 0).X.IsStrictlyGE 0 :=
  postnikov_lowerBound R B.obj 0
local instance zeroLeg_C_lowerBound : (postnikov R C.obj 0).X.IsStrictlyGE 0 :=
  postnikov_lowerBound R C.obj 0
local instance zeroLeg_B_nonpositive : (postnikov R B.obj 0).X.IsStrictlyLE 0 :=
  postnikov_nonpositive R B.obj 0

def postnikovZeroLeg (a : T ⟶ postnikov R B.obj n) :
    postnikov R T 0 ⟶ postnikov R B.obj 0 :=
  postnikovDesc R 0 (a ≫ postnikovTransition R B.obj n 0 hn)

lemma postnikovZeroLeg_projection (a : T ⟶ postnikov R B.obj n) :
    postnikovQuotient R T 0 ≫ postnikovZeroLeg R n hn B a =
      a ≫ postnikovTransition R B.obj n 0 hn := postnikovQuotient_desc R 0 _

lemma postnikovZeroLeg_isIso (a : T ⟶ postnikov R B.obj n) (ha : QuasiIso a.hom) :
    IsIso (postnikovZeroLeg R n hn B a) := by
  have := groups_map_isIso_of_quasiIso R a ha 0
  have := groups_map_isIso_of_quasiIsoAt R (postnikovTransition R B.obj n 0 hn) 0
    (postnikovTransition_quasiIsoAt R B.obj n 0 hn 0 (by omega))
  apply postnikovDesc_zero_isIso_of_groups R
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

lemma postnikovZeroLeg_square (a : T ⟶ postnikov R B.obj n) (b : U ⟶ T)
    (e : U ⟶ postnikov R C.obj n) (t : C ⟶ B)
    (h : b ≫ a = e ≫ postnikovMap R t.hom n) :
    postnikovMap R b 0 ≫ postnikovZeroLeg R n hn B a =
      postnikovZeroLeg R n hn C e ≫ postnikovMap R t.hom 0 := by
  have he : b ≫ (a ≫ postnikovTransition R B.obj n 0 hn) =
      (e ≫ postnikovTransition R C.obj n 0 hn) ≫ postnikovMap R t.hom 0 := by
    rw [← Category.assoc, h, Category.assoc, postnikovTransition_naturality,
      ← Category.assoc]
  exact (postnikovDesc_precompose R 0 b _).trans
    ((congrArg (fun z => postnikovDesc R 0 z) he).trans
      (postnikovDesc_postcompose R 0 _ (postnikovMap R t.hom 0)).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
