module

public import SerrePositivity.AlgebraicGeometry.FiniteIdealColimitFamilyModel
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
概要：逆極限の有限個のアフィン開上のイデアルを、同じ段の開の全体切断へ降ろす。
方針：opensCone の実際の極限と Γ の colimit を使い、有限族の環の模型を選ぶ。
規約：Stacks 0B8W (3)。局所模型はまだ大域イデアル層へ延長していない。
使われ方：C03 の有限アフィン被覆上の生成元の模型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 逆極限の有限個のアフィン開上の有限生成イデアルは、同じ段の開に模型を持つ。 -/
theorem exists_fg_ideal_family_model_of_affineOpen_limit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : J) {ι : Type u} [Finite ι] (U : ι → (D.obj i).affineOpens)
    (K : ∀ a, Ideal Γ((c.π.app i ⁻¹ᵁ (U a).1).toScheme, ⊤))
    (hK : ∀ a, (K a).FG) :
    ∃ (j : Over i) (L : ∀ a, Ideal Γ((D.map j.hom ⁻¹ᵁ (U a).1).toScheme, ⊤)),
      (∀ a, (L a).FG) ∧ ∀ a,
        (L a).map (((opensCone D c i (U a).1).π.app j).appTop).hom = K a := by
  let F (a : ι) := (opensDiagram D i (U a).1).op ⋙ Scheme.Γ
  let C (a : ι) := Scheme.Γ.mapCocone (opensCone D c i (U a).1).op
  have (a : ι) (j : Over i) : IsAffine ((opensDiagram D i (U a).1).obj j) :=
    (U a).2.preimage (D.map j.hom)
  have (a : ι) (j : (Over i)ᵒᵖ) : IsAffine (((opensDiagram D i (U a).1).op.obj j).unop) :=
    (U a).2.preimage (D.map j.unop.hom)
  have hC (a : ι) : IsColimit (C a) :=
    isColimitOfPreserves Scheme.Γ (isLimitOpensCone D c hc i (U a).1).op
  obtain ⟨j, L, hL, heq⟩ :=
    exists_fg_ideal_family_model_of_isColimit F C hC K hK
  exact ⟨j.unop, L, hL, heq⟩

end SerrePositivity.AlgebraicGeometry
