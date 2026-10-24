module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLift

/-!
概要：元の三代数の共通下界を、実経路模型とその非正次数 cover に保持する。
方針：実 cocone の二座標で恒等射の零性を証明し、複体同型と単射で移す。
規約：ホモロジーだけの下界で代用しない。使われ方：二切断対角模型の下界 −2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma cochainBiprod_lowerBound (K L : Complex R) (k : ℤ)
    [K.IsStrictlyGE k] [L.IsStrictlyGE k] : (K ⊞ L).IsStrictlyGE k := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  have hf : (biprod.fst : K ⊞ L ⟶ K).f i = 0 :=
    (K.isZero_of_isStrictlyGE k i hi).eq_of_tgt _ _
  have hg : (biprod.snd : K ⊞ L ⟶ L).f i = 0 :=
    (L.isZero_of_isStrictlyGE k i hi).eq_of_tgt _ _
  have ht := congrArg (fun t : K ⊞ L ⟶ K ⊞ L => t.f i) (biprod.total (X := K) (Y := L))
  change (biprod.fst : K ⊞ L ⟶ K).f i ≫ (biprod.inl : K ⟶ K ⊞ L).f i +
    (biprod.snd : K ⊞ L ⟶ L).f i ≫ (biprod.inr : L ⟶ K ⊞ L).f i = 𝟙 _ at ht
  simpa only [hf, hg, zero_comp, add_zero] using ht.symm

lemma cochainCocone_lowerBound {K L : Complex R} (f : K ⟶ L) (k : ℤ)
    [K.IsStrictlyGE k] [L.IsStrictlyGE k] : (mappingCocone f).IsStrictlyGE k := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  have hk := K.isZero_of_isStrictlyGE k i hi
  have hl := L.isZero_of_isStrictlyGE k (i - 1) (by omega)
  have hfst : (mappingCocone.fst f).f i = 0 := hk.eq_of_tgt _ _
  have hsnd : (mappingCocone.snd f).v i (i - 1) (by omega) = 0 := hl.eq_of_tgt _ _
  rw [← mappingCocone.id_X f i (i - 1) (by omega), hfst, hsnd]
  simp

lemma HomotopyPullbackModel.lowerBound {A B C : Mon (Complex R)}
    (f : A ⟶ B) (g : C ⟶ B) (k : ℤ)
    [A.X.IsStrictlyGE k] [B.X.IsStrictlyGE k] [C.X.IsStrictlyGE k] :
    (HomotopyPullbackModel.algebra R f g).X.IsStrictlyGE k := by
  have : (A.X ⊞ C.X).IsStrictlyGE k := cochainBiprod_lowerBound R _ _ k
  have : (mappingCocone (HomotopyPullbackModel.difference R f g)).IsStrictlyGE k :=
    cochainCocone_lowerBound R _ k
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  exact ((mappingCocone (HomotopyPullbackModel.difference R f g)).isZero_of_isStrictlyGE
    k i hi).of_iso (((HomologicalComplex.eval _ _ i).mapIso
      (HomotopyPullbackModel.complexIso R f g)))

lemma connectiveCover_lowerBound (A : Mon (Complex R)) (k : ℤ) [A.X.IsStrictlyGE k] :
    (connectiveCover R A).X.IsStrictlyGE k := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  exact IsZero.of_mono ((coverInclusion R A).f i) (A.X.isZero_of_isStrictlyGE k i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
