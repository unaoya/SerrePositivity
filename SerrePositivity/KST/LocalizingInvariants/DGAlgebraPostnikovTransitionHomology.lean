module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayer

/-!
概要：実 Postnikov 遷移射の全射性と、保持される次数のホモロジー同型を証明する。
方針：元の二つの商射との合成式を使い、全射性と準同型性を消去する。
規約：元の遷移射を保持。使われ方：隣接切断の kernel の長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (m n : ℤ) (h : n ≤ m)

lemma postnikovTransition_hom_factor :
    B.X.πTruncGE (-m) ≫ (postnikovTransition R B m n h).hom = B.X.πTruncGE (-n) :=
  congrArg Mon.Hom.hom (postnikovQuotient_transition R B m n h)

instance postnikovTransition_epi : Epi (postnikovTransition R B m n h).hom :=
  epi_of_epi_fac (postnikovTransition_hom_factor R B m n h)

instance postnikovTransition_component_epi (i : ℤ) :
    Epi ((postnikovTransition R B m n h).hom.f i) := by
  have hf := congrArg (fun f ↦ f.f i) (postnikovTransition_hom_factor R B m n h)
  change (B.X.πTruncGE (-m)).f i ≫ (postnikovTransition R B m n h).hom.f i =
    (B.X.πTruncGE (-n)).f i at hf
  exact epi_of_epi_fac hf

lemma postnikovTransition_quasiIsoAt (i : ℤ) (hi : -n ≤ i) :
    QuasiIsoAt (postnikovTransition R B m n h).hom i := by
  have : QuasiIsoAt (B.X.πTruncGE (-m)) i :=
    CochainComplex.quasiIsoAt_πTruncGE _ _ _ (by omega)
  have : QuasiIsoAt
      (B.X.πTruncGE (-m) ≫ (postnikovTransition R B m n h).hom) i := by
    rw [postnikovTransition_hom_factor]
    exact CochainComplex.quasiIsoAt_πTruncGE _ _ _ hi
  exact quasiIsoAt_of_comp_left (B.X.πTruncGE (-m))
    (postnikovTransition R B m n h).hom i

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
