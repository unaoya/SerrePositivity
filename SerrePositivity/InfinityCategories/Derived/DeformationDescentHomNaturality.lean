module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompAlgebra
/-!
概要：元の実変形降下比較を、任意の全関手射に自然な比較へ拡張する。
方針：同じ円柱の交換則と、制限比較の自然性四角形を合成する。
規約：変換の可逆性を仮定しない。使われ方：ξ の非可逆射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma deformationFunctorDescentHomotopy_hom_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    {T₀ T₁ : X ⟶ Y} (e : FunctorHom T₀ T₁) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₀)) ≫ e =
    (SSet.mapHomotopyCategory ((pre L).app Y)).map
      ((SSet.mapHomotopyCategory ((pre I).app Y)).map e) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy L I H T₁)) := by
  have he : HEq
      ((SSet.mapHomotopyCategory ((pre L).app Y)).map
        ((SSet.mapHomotopyCategory ((pre I).app Y)).map e))
      ((SSet.mapHomotopyCategory ((pre (L ≫ I)).app Y)).map e) :=
    heq_of_eq (functorHom_precomp_precomp e I L)
  have hL := functorHom_comp_heq
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp H T₀)))
    ((SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y)).map e)
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₀))) e
    (Category.assoc L I T₀) (Category.id_comp T₀) (Category.id_comp T₁)
    (functorHomotopyHom_heq_of_raw_eq _ _ rfl) (heq_of_eq (functorHom_precomp_id e))
  have hR := functorHom_comp_heq
    (f := (L ≫ I) ≫ T₀) (g := (L ≫ I) ≫ T₁) (h := T₁)
    (f' := L ≫ I ≫ T₀) (g' := L ≫ I ≫ T₁) (h' := T₁)
    ((SSet.mapHomotopyCategory ((pre (L ≫ I)).app Y)).map e)
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp H T₁)))
    ((SSet.mapHomotopyCategory ((pre L).app Y)).map
      ((SSet.mapHomotopyCategory ((pre I).app Y)).map e))
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (deformationFunctorDescentHomotopy L I H T₁)))
    (Category.assoc L I T₀) (Category.assoc L I T₁) (Category.id_comp T₁) he.symm
    (functorHomotopyHom_heq_of_raw_eq _ _ rfl)
  exact eq_of_heq (hL.symm.trans
    ((heq_of_eq (homotopy_postcomp_hom_exchange H e)).trans hR))
lemma deformationFunctorDescentIso_hom_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T U : X ⟶ Y) (hT : InvertsEdges T W) (hU : InvertsEdges U W)
    (a : FunctorHom T U) :
    (deformationFunctorDescentIso L I W H hH T hT).hom ≫ a =
      (SSet.mapHomotopyCategory ((pre L).app Y)).map
        ((SSet.mapHomotopyCategory ((pre I).app Y)).map a) ≫
          (deformationFunctorDescentIso L I W H hH U hU).hom := by
  simp only [deformationFunctorDescentIso_hom]
  exact deformationFunctorDescentHomotopy_hom_naturality L I H a
lemma deformationComparisonIso_hom_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T U : X ⟶ Y) (hT : InvertsEdges T W) (hU : InvertsEdges U W)
    {K K' : D ⟶ Y} (r : FunctorIso K (I ≫ T)) (s : FunctorIso K' (I ≫ U))
    (b : FunctorHom K K') (a : FunctorHom T U)
    (hs : b ≫ s.hom = r.hom ≫
      (SSet.mapHomotopyCategory ((pre I).app Y)).map a) :
    (r.precomp L ≪≫ deformationFunctorDescentIso L I W H hH T hT).hom ≫ a =
      (SSet.mapHomotopyCategory ((pre L).app Y)).map b ≫
        (s.precomp L ≪≫ deformationFunctorDescentIso L I W H hH U hU).hom := by
  have hp := congrArg (fun z => (SSet.mapHomotopyCategory ((pre L).app Y)).map z) hs
  simp only [CategoryTheory.Functor.map_comp] at hp
  have hp' : (r.precomp L).hom ≫
      (SSet.mapHomotopyCategory ((pre L).app Y)).map
        ((SSet.mapHomotopyCategory ((pre I).app Y)).map a) =
      (SSet.mapHomotopyCategory ((pre L).app Y)).map b ≫ (s.precomp L).hom := by
    simpa only [F2.functorIso_precomp_hom] using! hp.symm
  simp only [Iso.trans_hom, Category.assoc]
  rw [deformationFunctorDescentIso_hom_naturality, ← Category.assoc, hp', Category.assoc]
end
end SerrePositivity.InfinityCategories
