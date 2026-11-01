module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverFaithful

/-!
# 指定始点からの射列の持ち上げ終点

概要：元の基底射列の値から実際の持ち上げ終点を回収する。
方針：pathStar の像の等式から基底頂点と射列を回収し、終点の式を使う。
規約：終点の頂点そのものを同定する。
使われ方：指定した両端の間の射列の一意な持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma pathStar_endpoint (x : Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := quiver A
    ∀ q : Quiver.PathStar x, (projection A).pathStar x q = ⟨B, p⟩ →
      q.1 = (⟨B, x.path ≫ positiveEvaluation.map p⟩ : Vertex A) := by
  let := quiver A
  rintro ⟨⟨E, γ⟩, q⟩ h
  obtain ⟨hb, hp⟩ := Sigma.mk.inj_iff.mp h
  change E = B at hb
  subst B
  have hpath : (projection A).mapPath q = p := eq_of_heq hp
  have he := positive_endpoint A x (⟨E, γ⟩ : Vertex A) q
  rw [hpath] at he
  exact Vertex.ext rfl (heq_of_eq he.symm)

lemma liftPath_endpoint (x : Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := quiver A
    (liftPath A x p).1 = (⟨B, x.path ≫ positiveEvaluation.map p⟩ : Vertex A) := by
  let := quiver A
  exact pathStar_endpoint A x p _ (liftPath_projection A x p)

lemma liftPathTo_endpoint (x y : Vertex A) (p : Quiver.Path x.base y.base)
    (h : x.path ≫ positiveEvaluation.map p = y.path) :
    letI := quiver A
    (liftPath A x p).1 = y := by
  let := quiver A
  exact (liftPath_endpoint A x p).trans (Vertex.ext rfl (heq_of_eq h))

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
