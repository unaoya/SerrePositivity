module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverPositivePaths

/-!
# 元の基底射列の指定始点からの持ち上げと全データの一意性

概要：元の射列を持ち上げ、その基底射列・持ち上げ終点・全射列を回収する。
方針：元の pathStar の全単射を使う。
規約：基底の射列の像だけでなく実際の持ち上げ全体を扱う。
使われ方：元の hammock の行と縦射の同時持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def liftPath (x : Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := quiver A
    Quiver.PathStar x := by
  letI := quiver A
  exact (pathStarEquiv A x).symm ⟨B, p⟩

lemma liftPath_projection (x : Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := quiver A
    (projection A).pathStar x (liftPath A x p) = ⟨B, p⟩ := by
  let := quiver A
  exact (pathStarEquiv A x).apply_symm_apply ⟨B, p⟩

lemma lifted_pathStar_unique (x : Vertex A) :
    letI := quiver A
    ∀ p q : Quiver.PathStar x,
      (projection A).pathStar x p = (projection A).pathStar x q → p = q := by
  let := quiver A
  exact (pathStarEquiv A x).injective

lemma liftPath_unique (x : Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := quiver A
    ∀ q : Quiver.PathStar x, (projection A).pathStar x q = ⟨B, p⟩ → q = liftPath A x p := by
  let := quiver A
  intro q hq
  exact lifted_pathStar_unique A x q (liftPath A x p) (hq.trans (liftPath_projection A x p).symm)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
