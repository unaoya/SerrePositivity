module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.TammeSplitting
public import SerrePositivity.KST.LocalizingInvariants.InvariantZeroMap

/-!
概要：元の lax pullback の二射影の値を実積への一つの射にし、両包含上の作用を計算する。
方針：両射影の厳密な合成式と零関手の像の零性を、実積の外延性へ渡す。
規約：射影は元の完全関手。使われ方：両射影を保つ Tamme の積同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def laxValueProjectionHom : SpectrumHo.obj (value Φ (laxCategory p q)) ⟶
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  Binary.hoLift (SpectrumHo.hom (valueMap Φ (laxFst p q)))
    (SpectrumHo.hom (valueMap Φ (laxSnd p q)))

lemma laxValueProjectionHom_fst : laxValueProjectionHom Φ p q ≫
    SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      SpectrumHo.hom (valueMap Φ (laxFst p q)) := Binary.hoLift_fst _ _

lemma laxValueProjectionHom_snd : laxValueProjectionHom Φ p q ≫
    SpectrumHo.hom (Binary.snd (value Φ C) (value Φ D)) =
      SpectrumHo.hom (valueMap Φ (laxSnd p q)) := Binary.hoLift_snd _ _

namespace IsLocalizingInvariant
variable {Φ} (hΦ : IsLocalizingInvariant Φ)

include hΦ in
lemma laxValueProjectionHom_fromC :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫ laxValueProjectionHom Φ p q =
      SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) := by
  have hc : SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
      SpectrumHo.hom (valueMap Φ (laxFst p q)) = 𝟙 _ := by
    have hcomp : (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ laxFst p q = 𝟙 C :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (LaxInclusion.fromC_fst p q)
    have h := (stableValueFunctor Φ).map_comp
      (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) (laxFst p q)
    rw [hcomp, CategoryTheory.Functor.map_id] at h
    exact h.symm
  have hd : SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
      SpectrumHo.hom (valueMap Φ (laxSnd p q)) = 0 := by
    let F : C ⟶ D := (LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ laxSnd p q
    have h := hΦ.valueMap_hom_zero_of_zero_values F (by
        intro c
        change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((LaxInclusion.fromC p q ≫ (laxSnd p q).hom).app _ c)
        rw [LaxInclusion.fromC_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
        exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).isZero)
    change (stableValueFunctor Φ).map
      ((LaxInclusion.exactFromC p q : C ⟶ laxCategory p q) ≫ (laxSnd p q : laxCategory p q ⟶ D)) =
        0 at h
    rw [Functor.map_comp] at h
    exact h
  apply Binary.ho_hom_ext
  · rw [Category.assoc, laxValueProjectionHom_fst, hc, Binary.ho_inl_fst]
  · rw [Category.assoc, laxValueProjectionHom_snd, hd, Binary.ho_inl_snd]

include hΦ in
lemma laxValueProjectionHom_fromD :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫ laxValueProjectionHom Φ p q =
      SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) := by
  have hc : SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ (laxFst p q)) = 0 := by
    let F : D ⟶ C := (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ laxFst p q
    have h := hΦ.valueMap_hom_zero_of_zero_values F (by
        intro d
        change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((LaxInclusion.fromD p q ≫ (laxFst p q).hom).app _ d)
        rw [LaxInclusion.fromD_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
        exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isZero)
    change (stableValueFunctor Φ).map
      ((LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ (laxFst p q : laxCategory p q ⟶ C)) =
        0 at h
    rw [Functor.map_comp] at h
    exact h
  have hd : SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ (laxSnd p q)) = 𝟙 _ := by
    have hcomp : (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) ≫ laxSnd p q = 𝟙 D :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (LaxInclusion.fromD_snd p q)
    have h := (stableValueFunctor Φ).map_comp
      (LaxInclusion.exactFromD p q : D ⟶ laxCategory p q) (laxSnd p q)
    rw [hcomp, CategoryTheory.Functor.map_id] at h
    exact h.symm
  apply Binary.ho_hom_ext
  · rw [Category.assoc, laxValueProjectionHom_fst, hc, Binary.ho_inr_fst]
  · rw [Category.assoc, laxValueProjectionHom_snd, hd, Binary.ho_inr_snd]

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
