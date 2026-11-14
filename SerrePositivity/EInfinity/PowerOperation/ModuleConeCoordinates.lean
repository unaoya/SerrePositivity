module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# 同じ加群複体の cone の直積座標

DAG XIII Construction 2.2.6 の全 Hom と cone の指定比較に用いる補助。
同じ cone の二つの射影を、選んだ直積座標に厳密に同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {R : Type u} [CommRing R] {M N : CochainComplex (ModuleCat.{v} R) ℤ} (f : M ⟶ N)

/-- 同じ cone の各次数の直積座標。 -/
def moduleConePairIso (n : ℤ) :
    (mappingCone f).X n ≅ ModuleCat.of R (M.X (n + 1) × N.X n) :=
  homotopyCofiber.XIsoBiprod f n (n + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

lemma moduleConePairIso_inv_fst (n : ℤ) :
    (moduleConePairIso f n).inv ≫ homotopyCofiber.fstX f n (n + 1) rfl =
      ModuleCat.ofHom (LinearMap.fst R _ _) := by
  simp [moduleConePairIso, homotopyCofiber.fstX, Category.assoc]

lemma moduleConePairIso_inv_snd (n : ℤ) :
    (moduleConePairIso f n).inv ≫ homotopyCofiber.sndX f n =
      ModuleCat.ofHom (LinearMap.snd R _ _) := by
  have hs : homotopyCofiber.sndX f n =
      (homotopyCofiber.XIsoBiprod f n (n + 1) rfl).hom ≫ biprod.snd := by
    apply homotopyCofiber.ext_from_X f (n + 1) n rfl <;> simp
  rw [hs]
  simp [moduleConePairIso, Category.assoc]

lemma moduleConePairIso_hom_fst (n : ℤ) :
    (moduleConePairIso f n).hom ≫ ModuleCat.ofHom (LinearMap.fst R _ _) =
      homotopyCofiber.fstX f n (n + 1) rfl := by
  apply (cancel_epi (moduleConePairIso f n).inv).mp
  simp only [Iso.inv_hom_id_assoc, moduleConePairIso_inv_fst]

lemma moduleConePairIso_hom_snd (n : ℤ) :
    (moduleConePairIso f n).hom ≫ ModuleCat.ofHom (LinearMap.snd R _ _) =
      homotopyCofiber.sndX f n := by
  apply (cancel_epi (moduleConePairIso f n).inv).mp
  simp only [Iso.inv_hom_id_assoc, moduleConePairIso_inv_snd]

/-- 同じ cone の微分を直積座標に移した公式。 -/
lemma moduleConePairIso_d (n : ℤ) (x : M.X (n + 1) × N.X n) :
    (moduleConePairIso f (n + 1)).hom
      ((mappingCone f).d n (n + 1) ((moduleConePairIso f n).inv x)) =
      (-(M.d (n + 1) (n + 1 + 1) x.1), f.f (n + 1) x.1 + N.d n (n + 1) x.2) := by
  apply Prod.ext
  · change ((moduleConePairIso f n).inv ≫ (mappingCone f).d n (n + 1) ≫
      (moduleConePairIso f (n + 1)).hom ≫ ModuleCat.ofHom (LinearMap.fst R _ _)) x = _
    rw [moduleConePairIso_hom_fst]
    change ((moduleConePairIso f n).inv ≫ homotopyCofiber.d f n (n + 1) ≫
      homotopyCofiber.fstX f (n + 1) (n + 1 + 1) rfl) x = _
    rw [homotopyCofiber.d_fstX f n (n + 1) (n + 1 + 1) rfl rfl,
      Preadditive.comp_neg, ← Category.assoc,
      moduleConePairIso_inv_fst]
    rfl
  · change ((moduleConePairIso f n).inv ≫ (mappingCone f).d n (n + 1) ≫
      (moduleConePairIso f (n + 1)).hom ≫ ModuleCat.ofHom (LinearMap.snd R _ _)) x = _
    rw [moduleConePairIso_hom_snd]
    change ((moduleConePairIso f n).inv ≫ homotopyCofiber.d f n (n + 1) ≫
      homotopyCofiber.sndX f (n + 1)) x = _
    rw [homotopyCofiber.d_sndX f n (n + 1) rfl, Preadditive.comp_add]
    simp only [← Category.assoc, moduleConePairIso_inv_fst, moduleConePairIso_inv_snd]
    rfl

end SerrePositivity.EInfinity.PowerOperation
