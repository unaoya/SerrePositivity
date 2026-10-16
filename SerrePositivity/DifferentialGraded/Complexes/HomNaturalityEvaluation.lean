module
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 主Homの可換式を斉次要素へ評価する -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma hom_naturality_apply {H X X' Y Y' : Complex A}
    (F : H ⟶ homComplex A X X') (G : H ⟶ homComplex A Y Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : F ≫ homPostcompose X b = G ≫ homPrecompose a Y')
    {p i n : ℤ} (hn : i + p = n) (g : H.X p) (x : X.X i) :
    b.f n ((F.f p g).v i n hn x) = (G.f p g).v i n hn (a.f i x) := by
  have hh := congrArg (fun k : H ⟶ homComplex A X Y' => k.f p g) h
  rw [chain_comp_apply, chain_comp_apply, homPostcompose_apply, homPrecompose_apply] at hh
  have hv := congrArg (fun k : Cochain X Y' p => k.v i n hn x) hh
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply] at hv
  exact hv

end SerrePositivity.DifferentialGraded
