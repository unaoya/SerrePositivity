module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverEvaluation

/-!
# 元の対称化した持ち上げ射列の終点の回収

概要：持ち上げた射列の終点の groupoid の矢は始点の矢と元の射列の値の合成である。
方針：元の正向き・逆向きの矢の等式を元の射列の長さで反復する。
規約：実際の持ち上げ終点と元の商の矢を回収する。
使われ方：根からの連結性と元の hammock の固定端点の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma coverEvaluation_arrow (x y : Vertex A) :
    letI := quiver A
    ∀ f : @Quiver.Hom (Quiver.Symmetrify (Vertex A))
        (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) x y,
      x.path ≫ (coverEvaluation A).map f.toPath = y.path := by
  let := quiver A
  intro f
  change (x ⟶ y) ⊕ (y ⟶ x) at f
  cases f with
  | inl f =>
    change x.path ≫ symmetricEvaluation.map f.val.toPosPath = y.path
    exact f.property
  | inr f =>
    change x.path ≫ symmetricEvaluation.map f.val.toNegPath = y.path
    rw [evaluation_negative]
    have he := congrArg (fun p => p ≫ inv ((Quiver.FreeGroupoid.of Q).map f.val)) f.property
    have hp : y.path = x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f.val) := by
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he
    exact hp.symm

lemma coverEvaluation_endpoint (x y : Vertex A) :
    letI := quiver A
    ∀ p : @Quiver.Path (Quiver.Symmetrify (Vertex A))
        (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) x y,
      x.path ≫ (coverEvaluation A).map p = y.path := by
  let := quiver A
  intro p
  induction p with
  | nil =>
    change x.path ≫ (coverEvaluation A).map (𝟙 _) = x.path
    exact (congrArg (fun q => x.path ≫ q) ((coverEvaluation A).map_id x)).trans
      (Category.comp_id x.path)
  | @cons y z p f ih =>
    have hc : (coverEvaluation A).map
        (@Quiver.Path.cons (Quiver.Symmetrify (Vertex A))
          (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) x y z p f) =
        (coverEvaluation A).map p ≫ (coverEvaluation A).map
          (@Quiver.Hom.toPath (Quiver.Symmetrify (Vertex A))
            (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) y z f) :=
      (coverEvaluation A).map_comp p
        (@Quiver.Hom.toPath (Quiver.Symmetrify (Vertex A))
          (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) y z f)
    rw [hc, ← Category.assoc, ih]
    exact coverEvaluation_arrow A y z f

lemma projected_endpoint (x y : Vertex A) :
    letI := quiver A
    ∀ p : @Quiver.Path (Quiver.Symmetrify (Vertex A))
        (@Quiver.symmetrifyQuiver (Vertex A) (quiver A)) x y,
      x.path ≫ symmetricEvaluation.map ((symmetricProjection A).mapPath p) = y.path := by
  let := quiver A
  intro p
  exact coverEvaluation_endpoint A x y p

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
