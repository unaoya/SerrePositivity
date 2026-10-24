module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreZeroInverse

/-!
概要：同じ共通零底の実逆から、元の分子・分母の厳密な右底三角形を回収する。
方針：底の一致と同じ実逆の右三角形を合成し、元の塔の遷移の合成則を使う。
規約：指定した細分と逆を保持。使われ方：右係数三角形の class 標的への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n) {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (d : ZeroInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonZeroInverse_right_base :
    PostnikovRoofZeroSpan.numerator R n hn f (c.refine R d.source_le) ≫
      postnikovMap R (f.app i).hom 0 =
    PostnikovRoofZeroSpan.denominator R n hn f (c.refine R d.source_le) ≫
      postnikovMap R (B.transition (d.inverse_le.trans d.stage_le)).hom 0 := by
  have ht : postnikovMap R (B.transition d.stage_le).hom 0 ≫
      postnikovMap R (B.transition d.inverse_le).hom 0 =
      postnikovMap R (B.transition (d.inverse_le.trans d.stage_le)).hom 0 :=
    ((postnikovFunctor R 0).map_comp (B.transition d.stage_le)
      (B.transition d.inverse_le)).symm.trans
        (congrArg (fun t => (postnikovFunctor R 0).map t)
          (B.transition_comp d.stage_le d.inverse_le))
  calc
    _ = (PostnikovRoofZeroSpan.denominator R n hn f (c.refine R d.source_le) ≫
        postnikovMap R (B.transition d.stage_le).hom 0 ≫ d.inverse.base) ≫
          postnikovMap R (f.app i).hom 0 :=
      congrArg (fun t => t ≫ postnikovMap R (f.app i).hom 0) d.base_eq
    _ = PostnikovRoofZeroSpan.denominator R n hn f (c.refine R d.source_le) ≫
        postnikovMap R (B.transition d.stage_le).hom 0 ≫
          postnikovMap R (B.transition d.inverse_le).hom 0 := by
      simp only [Category.assoc, d.inverse.right_base]
    _ = _ := congrArg (fun t =>
      PostnikovRoofZeroSpan.denominator R n hn f (c.refine R d.source_le) ≫ t) ht

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
