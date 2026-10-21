module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverLiftPaths

/-!
# 元の被覆の自由圏の関手の忠実性

概要：同じ始点を持つ元の二つの持ち上げ射列は基底の射列で一意に決まる。
方針：実際の持ち上げ終点を含む pathStar の単射性を適用する。
規約：元の自由圏の関手そのものの忠実性を証明する。
使われ方：元の可換正方形と全 hammock の縦射の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma pathProjection_faithful : letI := quiver A; (pathProjection A).Faithful := by
  let := quiver A
  refine ⟨?_⟩
  intro x y p q h
  change Vertex A at x y
  change @Quiver.Path (Vertex A) (quiver A) x y at p q
  change (projection A).mapPath p = (projection A).mapPath q at h
  have he : (⟨y, p⟩ : Quiver.PathStar x) = ⟨y, q⟩ :=
    lifted_pathStar_unique A x ⟨y, p⟩ ⟨y, q⟩ (congrArg (Sigma.mk y.base) h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
