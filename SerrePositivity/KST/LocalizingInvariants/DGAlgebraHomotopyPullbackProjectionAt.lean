module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPairHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConnectingNaturality

/-!
概要：左脚の前次数全射性と同次数準同型性から、実 cospan の右射影を同次数で比較する。
方針：元の対の持ち上げで全射性を示し、接続像を左脚の像で消して単射性を示す。
規約：前次数の単射性は要求しない。使われ方：切断を底に持つレベル表示の連結度。
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

lemma right_quasiIsoAt_of_epi (n : ℤ)
    (hprev : Epi (homologyMap f.hom (n - 1))) (hcurr : QuasiIsoAt f.hom n) :
    QuasiIsoAt (right R f g).hom n := by
  have : IsIso (homologyMap f.hom n) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 hcurr
  have hinj := (ModuleCat.mono_iff_injective (homologyMap f.hom n)).1 inferInstance
  have hsurj := (ModuleCat.epi_iff_surjective (homologyMap f.hom n)).1 inferInstance
  have hprevSurj := (ModuleCat.epi_iff_surjective (homologyMap f.hom (n - 1))).1 hprev
  have hpair (x : (algebra R f g).X.homology n) :
      homologyMap f.hom n (homologyMap (left R f g).hom n x) =
        homologyMap g.hom n (homologyMap (right R f g).hom n x) := by
    let w : Path.Witness R (left R f g ≫ f) (right R f g ≫ g) :=
      ⟨path R _ _, path_source R _ _, path_target R _ _⟩
    have hh := congrArg (fun s => s x) (w.chainHomotopy.homologyMap_eq n)
    change homologyMap ((left R f g).hom ≫ f.hom) n x =
      homologyMap ((right R f g).hom ≫ g.hom) n x at hh
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh
  have hker (x : (algebra R f g).X.homology n)
      (hx : homologyMap (right R f g).hom n x = 0) : x = 0 := by
    have hfx : homologyMap f.hom n (homologyMap (left R f g).hom n x) =
        homologyMap f.hom n 0 := by rw [hpair x, hx, map_zero, map_zero]
    obtain ⟨z, hz⟩ := (connecting_pair_exact R f g n x).1 ⟨hinj hfx, hx⟩
    obtain ⟨a, ha⟩ := hprevSurj z
    have hzero : connecting R f g n (homologyMap f.hom (n - 1) a) = 0 := by
      change (homologyMap f.hom (n - 1) ≫ connecting R f g n) a = 0
      rw [left_connecting_zero]
      rfl
    exact hz.symm.trans ((congrArg (connecting R f g n) ha.symm).trans hzero)
  have : Mono (homologyMap (right R f g).hom n) := by
    apply (ModuleCat.mono_iff_injective _).2
    intro x y hxy
    have hz := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp hz
  have : Epi (homologyMap (right R f g).hom n) := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro y
    obtain ⟨x, hx⟩ := hsurj (homologyMap g.hom n y)
    obtain ⟨z, _, hz⟩ := homology_pair_lift R f g n x y hx
    exact ⟨z, hz⟩
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).2 (isIso_of_mono_of_epi _)

lemma right_connecting_zero (n : ℤ) :
    homologyMap g.hom (n - 1) ≫ connecting R f g n = 0 := by
  have hi : (Limits.biprod.inr : C.X ⟶ A.X ⊞ C.X) ≫ difference R f g = -g.hom := by
    simp only [difference, Limits.biprod.inr_desc]
  have hz := CochainComplex.homologyMap_homologyδOfTriangle
    (CochainComplex.mappingCocone.triangle (difference R f g))
    (DerivedCategory.mappingCocone_triangle_distinguished _)
    (n - 1) n (by omega)
  have hz' : homologyMap (difference R f g) (n - 1) ≫
      homologyδOfTriangle (mappingCocone.triangle (difference R f g))
        (n - 1) n (by omega) = 0 := hz
  have hzero : homologyMap (-g.hom) (n - 1) ≫ connecting R f g n = 0 := by
    unfold connecting
    rw [← hi, homologyMap_comp, Category.assoc,
      ← Category.assoc (homologyMap (difference R f g) (n - 1)), hz']
    simp
  rw [homologyMap_neg, Preadditive.neg_comp] at hzero
  exact neg_eq_zero.mp hzero

lemma left_quasiIsoAt_of_epi (n : ℤ)
    (hprev : Epi (homologyMap g.hom (n - 1))) (hcurr : QuasiIsoAt g.hom n) :
    QuasiIsoAt (left R f g).hom n := by
  have : IsIso (homologyMap g.hom n) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 hcurr
  have hinj := (ModuleCat.mono_iff_injective (homologyMap g.hom n)).1 inferInstance
  have hsurj := (ModuleCat.epi_iff_surjective (homologyMap g.hom n)).1 inferInstance
  have hprevSurj := (ModuleCat.epi_iff_surjective (homologyMap g.hom (n - 1))).1 hprev
  have hpair (x : (algebra R f g).X.homology n) :
      homologyMap g.hom n (homologyMap (right R f g).hom n x) =
        homologyMap f.hom n (homologyMap (left R f g).hom n x) := by
    let w : Path.Witness R (left R f g ≫ f) (right R f g ≫ g) :=
      ⟨path R _ _, path_source R _ _, path_target R _ _⟩
    have hh := congrArg (fun s => s x) (w.chainHomotopy.homologyMap_eq n)
    change homologyMap ((left R f g).hom ≫ f.hom) n x =
      homologyMap ((right R f g).hom ≫ g.hom) n x at hh
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh.symm
  have hker (x : (algebra R f g).X.homology n)
      (hx : homologyMap (left R f g).hom n x = 0) : x = 0 := by
    have hfx : homologyMap g.hom n (homologyMap (right R f g).hom n x) =
        homologyMap g.hom n 0 := by rw [hpair x, hx, map_zero, map_zero]
    obtain ⟨z, hz⟩ := (connecting_pair_exact R f g n x).1 ⟨hx, hinj hfx⟩
    obtain ⟨a, ha⟩ := hprevSurj z
    have hzero : connecting R f g n (homologyMap g.hom (n - 1) a) = 0 := by
      change (homologyMap g.hom (n - 1) ≫ connecting R f g n) a = 0
      rw [right_connecting_zero]
      rfl
    exact hz.symm.trans ((congrArg (connecting R f g n) ha.symm).trans hzero)
  have : Mono (homologyMap (left R f g).hom n) := by
    apply (ModuleCat.mono_iff_injective _).2
    intro x y hxy
    have hz := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp hz
  have : Epi (homologyMap (left R f g).hom n) := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro y
    obtain ⟨x, hx⟩ := hsurj (homologyMap f.hom n y)
    obtain ⟨z, hz, _⟩ := homology_pair_lift R f g n y x hx.symm
    exact ⟨z, hz⟩
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).2 (isIso_of_mono_of_epi _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
