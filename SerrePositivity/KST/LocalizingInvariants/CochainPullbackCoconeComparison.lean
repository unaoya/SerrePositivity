module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelCoconeQuasiIso

/-!
概要：通常の複体 pullback から二脚の差の cocone への標準比較。
方針：二射影の対を実 kernel と同定し、一脚の全射性から差の全射性を得る。
規約：比較 cochain は零に固定。使われ方：実 dg 代数 pullback の準同型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L T : Complex R} (f : K ⟶ T) (g : L ⟶ T)

abbrev cochainPullbackDifference : K ⊞ L ⟶ T := biprod.desc f (-g)

lemma cochainPullbackPair_condition :
    biprod.lift (pullback.fst f g) (pullback.snd f g) ≫
      cochainPullbackDifference f g = 0 := by
  simp only [cochainPullbackDifference, biprod.lift_desc, Preadditive.comp_neg,
    pullback.condition, add_neg_cancel]

def cochainPullbackToCocone : pullback f g ⟶ mappingCocone (cochainPullbackDifference f g) :=
  mappingCocone.lift _ (biprod.lift (pullback.fst f g) (pullback.snd f g)) 0
    (by rw [cochainPullbackPair_condition]; simp)

@[reassoc] lemma cochainPullbackToCocone_fst :
    cochainPullbackToCocone f g ≫ mappingCocone.fst (cochainPullbackDifference f g) =
      biprod.lift (pullback.fst f g) (pullback.snd f g) := mappingCocone.lift_fst _ _ _ _

lemma cochainPullbackToCocone_snd :
    (Cochain.ofHom (cochainPullbackToCocone f g)).comp
      (mappingCocone.snd (cochainPullbackDifference f g)) (zero_add (-1)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v]
  exact mappingCocone.lift_f_snd_v _
    (biprod.lift (pullback.fst f g) (pullback.snd f g)) 0 _ p q hpq

lemma cochainPullbackDifference_epi_left [Epi f] : Epi (cochainPullbackDifference f g) := by
  have h : (biprod.inl : K ⟶ K ⊞ L) ≫ cochainPullbackDifference f g = f := biprod.inl_desc _ _
  exact epi_of_epi_fac h

lemma cochainPullbackDifference_epi_right [Epi g] : Epi (cochainPullbackDifference f g) := by
  have h : (biprod.inr : L ⟶ K ⊞ L) ≫ cochainPullbackDifference f g = -g := biprod.inr_desc _ _
  exact epi_of_epi_fac h

lemma cochainPullbackToCocone_quasiIso [Epi (cochainPullbackDifference f g)] :
    QuasiIso (cochainPullbackToCocone f g) :=
  cochainKernelCoconeLift_quasiIso _ _ (cochainPullbackPair_condition f g)
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)

lemma cochainPullbackToCocone_quasiIso_left [Epi f] :
    QuasiIso (cochainPullbackToCocone f g) := by
  have := cochainPullbackDifference_epi_left f g
  exact cochainPullbackToCocone_quasiIso f g

lemma cochainPullbackToCocone_quasiIso_right [Epi g] :
    QuasiIso (cochainPullbackToCocone f g) := by
  have := cochainPullbackDifference_epi_right f g
  exact cochainPullbackToCocone_quasiIso f g

end SerrePositivity.KST.LocalizingInvariants
