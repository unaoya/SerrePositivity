module

public import SerrePositivity.KST.Spectra.PointedVerticalPaths
public import SerrePositivity.KST.Spectra.PostMappingFibration
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：構造比較区間の射影の両端点固定収縮から、同じ端点の垂直な構造区間を構成する。
方針：Hom への後合成の Kan fibration に収縮を持ち上げ、区間の境界全体を固定する。
規約：射影の収縮は入力。使われ方：非零境界での構造比較を相対厳密化へ渡す条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 射影の収縮を、元の区間の両端点を固定した変形へ持ち上げる。 -/
lemma exists_vertical_path_of_projection_contraction {T E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : J.rlp p.right) {f g : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (K : SSet.Homotopy (P.path ≫ (PointedObject.basedHomMap T p).right)
      (SSet.const (familyVertex (f ≫ p))))
    (hboundary : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ≫
        (PointedObject.basedHomMap T p).right) :
    ∃ Q : VerticalPath p f g, ∃ V : SSet.Homotopy P.path Q.path,
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ∧
      V.h ≫ (PointedObject.basedHomMap T p).right = K.h := by
  let pFibration : Fibration p.right := (fibration_iff _).2 hp
  let postFibration : Fibration (PointedObject.basedHomMap T p).right := post_fibration T p
  have hpost : J.rlp (PointedObject.basedHomMap T p).right := (fibration_iff _).1 inferInstance
  let a := (boundary 1).ι ≫ P.path
  let H : SSet.Homotopy a a := {
    h := fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a
    h₀ := by rfl
    h₁ := by rfl
    rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
  have hi : H.h ≫ (PointedObject.basedHomMap T p).right =
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h := by
    simpa only [H, a, Category.assoc] using hboundary.symm
  obtain ⟨l, hl, V, hV, hproj⟩ := KanFibrationEndpointExtension.exists_from_zero
    (PointedObject.basedHomMap T p).right hpost (boundary 1).ι P.path a H K.h K.h₀.symm hi
  have hlp : l ≫ (PointedObject.basedHomMap T p).right =
      SSet.const (familyVertex (f ≫ p)) := by
    have h := congrArg (SSet.ι₁ ≫ ·) hproj
    rw [← Category.assoc, V.h₁, K.h₁] at h
    exact h
  have hface (i : Fin 2) : stdSimplex.δ i ≫ l = stdSimplex.δ i ≫ P.path := by
    rw [← boundary.ι_ι i, Category.assoc, hl]
    rfl
  let Q : VerticalPath p f g := {
    path := l
    zero := (hface 1).trans P.zero
    one := (hface 0).trans P.one
    «over» := hlp }
  exact ⟨Q, V, hV, hproj⟩

/-- 両端点固定で垂直区間へ変形できるなら、その変形の射影が必要な収縮を与える。 -/
lemma exists_projection_contraction_of_vertical_path {T E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) {f g : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) (Q : VerticalPath p f g)
    (V : SSet.Homotopy P.path Q.path)
    (hboundary : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path) :
    ∃ K : SSet.Homotopy (P.path ≫ (PointedObject.basedHomMap T p).right)
        (SSet.const (familyVertex (f ≫ p))),
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ≫
          (PointedObject.basedHomMap T p).right := by
  let K : SSet.Homotopy (P.path ≫ (PointedObject.basedHomMap T p).right)
      (SSet.const (familyVertex (f ≫ p))) := {
    h := V.h ≫ (PointedObject.basedHomMap T p).right
    h₀ := by rw [← Category.assoc, V.h₀]; rfl
    h₁ := by rw [← Category.assoc, V.h₁, Q.over]; rfl
    rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
  refine ⟨K, ?_⟩
  change _ ≫ (V.h ≫ _) = _
  rw [← Category.assoc, hboundary]
  simp only [Category.assoc]

/-- 射影の両端点固定収縮は、同じ端点を固定した垂直区間への変形の必要十分条件。 -/
lemma projection_contraction_iff_vertical_deformation {T E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : J.rlp p.right) {f g : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) :
    (∃ K : SSet.Homotopy (P.path ≫ (PointedObject.basedHomMap T p).right)
        (SSet.const (familyVertex (f ≫ p))),
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ≫
          (PointedObject.basedHomMap T p).right) ↔
    (∃ Q : VerticalPath p f g, ∃ V : SSet.Homotopy P.path Q.path,
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path) := by
  constructor
  · rintro ⟨K, hb⟩
    obtain ⟨Q, V, hV, _⟩ := exists_vertical_path_of_projection_contraction p hp P K hb
    exact ⟨Q, V, hV⟩
  · rintro ⟨Q, V, hb⟩
    exact exists_projection_contraction_of_vertical_path p P Q V hb

end SerrePositivity.KST.Spectra.PointedMapping
