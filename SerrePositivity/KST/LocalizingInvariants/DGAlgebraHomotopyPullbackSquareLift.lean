module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProBase

/-!
概要：元の厳密可換な塔の正方形を、経路模型への実レベル射へ持ち上げる。
方針：元の合成の対角経路を使い、二脚と経路の三成分で自然性を検証する。
規約：高次錐の存在を入力しない。使われ方：有限 Postnikov 射の元の因子分解。
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
variable (R : Type u) [CommRing R] {W X Y Z : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom Z Y) (a : LevelHom W X) (b : LevelHom W Z)
  (hs : a.comp f = b.comp g)

def squareWitness (i : ℕ) : Path.Witness R (a.app i ≫ f.app i) (b.app i ≫ g.app i) where
  hom := (a.app i ≫ f.app i) ≫ Path.diagonal R (Y.obj i)
  source_eq := by rw [Category.assoc, Path.diagonal_source, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.diagonal_target, Category.comp_id]
    exact congrArg (fun c => c.app i) hs

def squareLiftApp (i : ℕ) : W.obj i ⟶ algebra R (f.app i) (g.app i) :=
  lift R (f.app i) (g.app i) (a.app i) (b.app i) (squareWitness R f g a b hs i)

lemma squareLiftApp_left (i : ℕ) :
    squareLiftApp R f g a b hs i ≫ left R (f.app i) (g.app i) = a.app i :=
  lift_left R _ _ _ _ _

lemma squareLiftApp_right (i : ℕ) :
    squareLiftApp R f g a b hs i ≫ right R (f.app i) (g.app i) = b.app i :=
  lift_right R _ _ _ _ _

lemma squareLiftApp_path (i : ℕ) :
    squareLiftApp R f g a b hs i ≫ path R (f.app i) (g.app i) =
      (a.app i ≫ f.app i) ≫ Path.diagonal R (Y.obj i) := lift_path R _ _ _ _ _

def squareTransition {m i : ℕ} (hi : i ≤ m) :
    algebra R (f.app m) (g.app m) ⟶ algebra R (f.app i) (g.app i) :=
  map R (f.app m) (g.app m) (f.app i) (g.app i)
    (X.transition hi) (Y.transition hi) (Z.transition hi)
    (f.naturality hi) (g.naturality hi)

lemma squareLiftApp_naturality {m i : ℕ} (hi : i ≤ m) :
    W.transition hi ≫ squareLiftApp R f g a b hs i =
      squareLiftApp R f g a b hs m ≫ squareTransition R f g hi := by
  have hl : squareTransition R f g hi ≫ left R (f.app i) (g.app i) =
      left R (f.app m) (g.app m) ≫ X.transition hi := map_left R _ _ _ _ _ _ _ _ _
  have hr : squareTransition R f g hi ≫ right R (f.app i) (g.app i) =
      right R (f.app m) (g.app m) ≫ Z.transition hi := map_right R _ _ _ _ _ _ _ _ _
  have hp : squareTransition R f g hi ≫ path R (f.app i) (g.app i) =
      path R (f.app m) (g.app m) ≫ Path.map R (Y.transition hi) :=
    map_path R _ _ _ _ _ _ _ _ _
  apply hom_ext R (f.app i) (g.app i)
  · rw [Category.assoc, squareLiftApp_left, Category.assoc, hl,
      ← Category.assoc, squareLiftApp_left]
    exact a.naturality hi
  · rw [Category.assoc, squareLiftApp_right, Category.assoc, hr,
      ← Category.assoc, squareLiftApp_right]
    exact b.naturality hi
  · calc
      (W.transition hi ≫ squareLiftApp R f g a b hs i) ≫ path R (f.app i) (g.app i) =
          W.transition hi ≫ ((a.app i ≫ f.app i) ≫ Path.diagonal R (Y.obj i)) := by
        rw [Category.assoc, squareLiftApp_path]
      _ = ((a.app m ≫ f.app m) ≫ Path.diagonal R (Y.obj m)) ≫
          Path.map R (Y.transition hi) := by
        have hn := congrArg (fun t => t ≫ Path.diagonal R (Y.obj i))
          ((a.comp f).naturality hi)
        change (W.transition hi ≫ (a.app i ≫ f.app i)) ≫ Path.diagonal R (Y.obj i) =
          ((a.app m ≫ f.app m) ≫ Y.transition hi) ≫ Path.diagonal R (Y.obj i) at hn
        have hd := congrArg (fun t => (a.app m ≫ f.app m) ≫ t)
          (Path.diagonal_naturality R (Y.transition hi))
        calc
          _ = (a.app m ≫ f.app m) ≫ (Y.transition hi ≫ Path.diagonal R (Y.obj i)) := by
            simpa only [Category.assoc] using hn
          _ = _ := by simpa only [Category.assoc] using hd.symm
      _ = (squareLiftApp R f g a b hs m ≫ squareTransition R f g hi) ≫
          path R (f.app i) (g.app i) := by
        symm
        calc
          _ = squareLiftApp R f g a b hs m ≫
              (squareTransition R f g hi ≫ path R (f.app i) (g.app i)) :=
            Category.assoc _ _ _
          _ = squareLiftApp R f g a b hs m ≫
              (path R (f.app m) (g.app m) ≫ Path.map R (Y.transition hi)) :=
            congrArg (fun t => squareLiftApp R f g a b hs m ≫ t) hp
          _ = (squareLiftApp R f g a b hs m ≫ path R (f.app m) (g.app m)) ≫
              Path.map R (Y.transition hi) := (Category.assoc _ _ _).symm
          _ = _ := congrArg (fun t => t ≫ Path.map R (Y.transition hi))
            (squareLiftApp_path R f g a b hs m)

/-- 両脚は入力の元の射で、経路も元の合成の対角を保つ。 -/
def squareLift : LevelHom W (modelTower R f g) where
  app := squareLiftApp R f g a b hs
  naturality hi := squareLiftApp_naturality R f g a b hs hi

lemma squareLift_comp_right : (squareLift R f g a b hs).comp (rightProjection R f g) = b := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact lift_right R _ _ _ _ _

lemma squareLift_comp_left : (squareLift R f g a b hs).comp (leftProjection R f g) = a := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact lift_left R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
