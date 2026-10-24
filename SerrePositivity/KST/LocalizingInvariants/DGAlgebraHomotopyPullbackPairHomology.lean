module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConnecting

/-!
概要：実 cospan 模型のホモロジーへ、元の二脚で一致する任意の対を持ち上げる。
方針：双積上の対を差の核へ入れ、実 cocone 完全列と複体同型で回収する。
規約：両射影を同時に保持する。使われ方：pullback の右射影の pro 像全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

lemma homology_pair_lift (n : ℤ) (x : A.X.homology n) (y : C.X.homology n)
    (hxy : homologyMap f.hom n x = homologyMap g.hom n y) :
    ∃ z : (algebra R f g).X.homology n,
      homologyMap (left R f g).hom n z = x ∧ homologyMap (right R f g).hom n z = y := by
  let pair := homologyMap (biprod.inl : A.X ⟶ A.X ⊞ C.X) n x +
    homologyMap (biprod.inr : C.X ⟶ A.X ⊞ C.X) n y
  have hz : homologyMap (difference R f g) n pair = 0 := by
    have hinl : (biprod.inl : A.X ⟶ A.X ⊞ C.X) ≫ difference R f g = f.hom := by
      simp only [difference, biprod.inl_desc]
    have hinr : (biprod.inr : C.X ⟶ A.X ⊞ C.X) ≫ difference R f g = -g.hom := by
      simp only [difference, biprod.inr_desc]
    simp only [pair, map_add, ← ModuleCat.comp_apply, ← homologyMap_comp,
      hinl, hinr, homologyMap_neg, hxy]
    change homologyMap g.hom n y + -(homologyMap g.hom n y) = 0
    exact add_neg_cancel _
  have hS := homologyMap_exact₂_of_distTriang (mappingCocone.triangle (difference R f g))
    (DerivedCategory.mappingCocone_triangle_distinguished _) n
  have he : Function.Exact (homologyMap (mappingCocone.fst (difference R f g)) n)
      (homologyMap (difference R f g) n) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS
  obtain ⟨w, hw⟩ := (he pair).1 hz
  let e := complexIso R f g
  refine ⟨homologyMap e.inv n w, ?_, ?_⟩
  · have hp := fromMappingCocone_left R f g
    change e.inv ≫ (left R f g).hom = _ at hp
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, hp]
    change homologyMap (mappingCocone.fst (difference R f g) ≫ biprod.fst) n w = x
    rw [homologyMap_comp, ModuleCat.comp_apply, hw]
    simp [pair, ← ModuleCat.comp_apply, ← homologyMap_comp]
  · have hp := fromMappingCocone_right R f g
    change e.inv ≫ (right R f g).hom = _ at hp
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, hp]
    change homologyMap (mappingCocone.fst (difference R f g) ≫ biprod.snd) n w = y
    rw [homologyMap_comp, ModuleCat.comp_apply, hw]
    simp [pair, ← ModuleCat.comp_apply, ← homologyMap_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
