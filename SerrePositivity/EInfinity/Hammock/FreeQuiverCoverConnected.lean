module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverEndpoint

/-!
# 元の根付き被覆の根からの連結性

概要：元の全持ち上げ頂点は固定根からの対称化した射列で到達できる。
方針：元の groupoid の矢の代表射列を持ち上げ、元の終点の回収式を使う。
規約：元の商の矢と実際の持ち上げ頂点を同定する。
使われ方：普遍被覆の木性と全指定自由圏の成分の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] {A : Q}

lemma Vertex.ext {x y : Vertex A} (hb : x.base = y.base) (hp : HEq x.path y.path) : x = y := by
  cases x
  cases y
  cases hb
  cases eq_of_heq hp
  rfl

abbrev symmetricPath (A : Q) (x y : Vertex A) : Type (max u v) :=
  @Quiver.Path (Quiver.Symmetrify (Vertex A))
    (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) x y

lemma root_connected (A : Q) (x : Vertex A) : Nonempty (symmetricPath A (root A) x) := by
  let := quiver A
  rcases x with ⟨B, β⟩
  refine Quot.inductionOn β ?_
  intro p
  change Quiver.Path (V := Quiver.Symmetrify Q) A B at p
  obtain ⟨⟨y, q⟩, hq⟩ := (symmetricPathStarEquiv A (root A)).surjective
    (⟨B, p⟩ : Quiver.PathStar (Quiver.Symmetrify.of.obj A))
  change Quiver.PathStar.mk ((symmetricProjection A).mapPath q) = Quiver.PathStar.mk p at hq
  obtain ⟨hb, hp⟩ := Sigma.mk.inj_iff.mp hq
  subst B
  have he := projected_endpoint A (root A) y q
  have hpath : (symmetricProjection A).mapPath q = p := eq_of_heq hp
  rw [hpath] at he
  have hv : symmetricEvaluation.map p = y.path := (Category.id_comp _).symm.trans he
  have hy : (⟨y.base, symmetricEvaluation.map p⟩ : Vertex A) = y :=
    Vertex.ext rfl (heq_of_eq hv)
  exact ⟨hy.symm ▸ q⟩

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
