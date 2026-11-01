module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverCostars

/-!
# 元の根付き被覆の全射列の一意な持ち上げ

概要：元の有向射列と対称化した射列は指定した始点から一意に持ち上がる。
方針：元の被覆性を Mathlib の射列の持ち上げと対称化の被覆性へ適用する。
規約：元の射列と実際の持ち上げ終点を保持する。
使われ方：元の hammock の全行と全縦射を持ち上げる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def pathStarEquiv (x : Vertex A) :
    letI := quiver A
    Quiver.PathStar x ≃ Quiver.PathStar x.base := by
  letI := quiver A
  exact Equiv.ofBijective ((projection A).pathStar x)
    ((projection_isCovering A).pathStar_bijective x)

lemma symmetrify_isCovering :
    letI := quiver A
    (projection A).symmetrify.IsCovering := by
  let := quiver A
  exact (projection_isCovering A).symmetrify

def symmetricPathStarEquiv (x : Vertex A) :
    letI := quiver A
    Quiver.PathStar (Quiver.Symmetrify.of.obj x) ≃
      Quiver.PathStar (Quiver.Symmetrify.of.obj x.base) := by
  letI := quiver A
  exact Equiv.ofBijective ((projection A).symmetrify.pathStar (Quiver.Symmetrify.of.obj x))
    ((symmetrify_isCovering A).pathStar_bijective _)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
