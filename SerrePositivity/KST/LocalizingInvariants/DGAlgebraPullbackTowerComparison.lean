module

public import SerrePositivity.KST.LocalizingInvariants.ProMonoidPullbackLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSquareLift

/-!
概要：元の通常 pullback の塔を、元の経路模型の塔へ両射影と経路を保って比較する。
方針：元の pullback 条件を厳密正方形の持ち上げに渡し、成分を元の比較射と同定。
規約：一脚の全射性は準同型性にだけ使う。使われ方：零底を揃えた実拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom Z Y)

lemma strictProjection_condition :
    (MonoidPullback.leftProjection f g).comp f = (MonoidPullback.rightProjection f g).comp g := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact MonoidPullback.condition (f.app i) (g.app i)

def strictComparison : LevelHom (MonoidPullback.pullbackTower f g) (modelTower R f g) :=
  squareLift R f g (MonoidPullback.leftProjection f g) (MonoidPullback.rightProjection f g)
    (strictProjection_condition R f g)

lemma strictComparison_app (i : ℕ) :
    (strictComparison R f g).app i = comparison R (f.app i) (g.app i) := by
  apply hom_ext R (f.app i) (g.app i)
  · exact (squareLiftApp_left R f g _ _ _ i).trans (comparison_left R _ _).symm
  · exact (squareLiftApp_right R f g _ _ _ i).trans (comparison_right R _ _).symm
  · exact (squareLiftApp_path R f g _ _ _ i).trans
      ((Category.assoc _ _ _).trans (comparison_path R _ _).symm)

lemma strictComparison_comp_left :
    (strictComparison R f g).comp (leftProjection R f g) = MonoidPullback.leftProjection f g :=
  squareLift_comp_left R _ _ _ _ _

lemma strictComparison_comp_right :
    (strictComparison R f g).comp (rightProjection R f g) = MonoidPullback.rightProjection f g :=
  squareLift_comp_right R _ _ _ _ _

lemma strictComparison_quasiIso_right (hg : ∀ i, Epi (g.app i).hom) (i : ℕ) :
    QuasiIso ((strictComparison R f g).app i).hom := by
  rw [strictComparison_app]
  have := hg i
  exact comparison_quasiIso_right R _ _

lemma strictComparison_squareLift {W : Tower (Mon (Complex R))}
    (a : LevelHom W X) (b : LevelHom W Z) (hs : a.comp f = b.comp g) :
    (MonoidPullback.squareLift f g a b hs).comp (strictComparison R f g) =
      squareLift R f g a b hs := by
  apply ProSpectrum.levelHom_ext
  intro i
  change MonoidPullback.squareLiftApp f g a b hs i ≫ (strictComparison R f g).app i =
    squareLiftApp R f g a b hs i
  rw [strictComparison_app]
  apply hom_ext R (f.app i) (g.app i)
  · rw [Category.assoc, comparison_left, MonoidPullback.squareLiftApp_fst, squareLiftApp_left]
  · rw [Category.assoc, comparison_right, MonoidPullback.squareLiftApp_snd, squareLiftApp_right]
  · let s := MonoidPullback.squareLiftApp f g a b hs i
    change (s ≫ comparison R (f.app i) (g.app i)) ≫ path R (f.app i) (g.app i) = _
    calc
      _ = s ≫ (comparison R (f.app i) (g.app i) ≫ path R (f.app i) (g.app i)) :=
        Category.assoc _ _ _
      _ = s ≫ (MonoidPullback.fst (f.app i) (g.app i) ≫
          f.app i ≫ Path.diagonal R (Y.obj i)) :=
        congrArg (fun t => s ≫ t) (comparison_path R _ _)
      _ = ((s ≫ MonoidPullback.fst (f.app i) (g.app i)) ≫ f.app i) ≫
          Path.diagonal R (Y.obj i) := by simp only [Category.assoc]
      _ = (a.app i ≫ f.app i) ≫ Path.diagonal R (Y.obj i) :=
        congrArg (fun t => (t ≫ f.app i) ≫ Path.diagonal R (Y.obj i))
          (MonoidPullback.squareLiftApp_fst f g a b hs i)
      _ = _ := (squareLiftApp_path R f g a b hs i).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
