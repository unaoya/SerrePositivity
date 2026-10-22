module

public import SerrePositivity.KST.LocalizingInvariants.DGBimodulePostnikov
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransition

/-!
概要：集中双加群の二つの底切断上の作用を、元の Postnikov 遷移に沿って比較する。
方針：元の商射と遷移の合成式、作用の回収式、tensor 全射性を使う。
規約：同じ underlying 係数を保持。使われ方：共通零底から元の roof 底への作用の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) [A.X.IsStrictlyLE 0]
  (M : Bimod A A) (k : ℤ) [M.X.IsStrictlyLE k] [M.X.IsStrictlyGE k]
  (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) (h : m ≤ n)

lemma postnikovBimodule_left_transition :
    ((postnikovTransition R A n m h).hom ▷ M.X) ≫
      (postnikovBimodule R A M k m hm).actLeft =
        (postnikovBimodule R A M k n hn).actLeft := by
  have : Epi (postnikovQuotient R A n).hom := TruncationDesc.projection_epi A.X (-n)
  have : Epi ((postnikovQuotient R A n).hom ▷ M.X) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi ((postnikovQuotient R A n).hom ▷ M.X)).1
  have he : (postnikovQuotient R A n).hom ≫ (postnikovTransition R A n m h).hom =
      (postnikovQuotient R A m).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_transition R A n m h)
  rw [← comp_whiskerRight_assoc, he, postnikovBimodule_left_projection,
    postnikovBimodule_left_projection]

lemma postnikovBimodule_right_transition :
    (M.X ◁ (postnikovTransition R A n m h).hom) ≫
      (postnikovBimodule R A M k m hm).actRight =
        (postnikovBimodule R A M k n hn).actRight := by
  have : Epi (postnikovQuotient R A n).hom := TruncationDesc.projection_epi A.X (-n)
  have : Epi (M.X ◁ (postnikovQuotient R A n).hom) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi (M.X ◁ (postnikovQuotient R A n).hom)).1
  have he : (postnikovQuotient R A n).hom ≫ (postnikovTransition R A n m h).hom =
      (postnikovQuotient R A m).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_transition R A n m h)
  rw [← whiskerLeft_comp_assoc, he, postnikovBimodule_right_projection,
    postnikovBimodule_right_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
