module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverSurjective

/-!
概要：非正次数代数の間の実 roof を、分母の次数全射準同型性を保って非正次数化する。
方針：頂点の connective cover から元の両脚へ合成し、閉元の実持ち上げを使う。
規約：元の両脚と反転関手での値を保持する。使われ方：高次 class cospan の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} [A.X.IsStrictlyLE 0]
  (r : SurjectiveRoof R A B)

def nonpositiveNormalization : SurjectiveRoof R A B where
  apex := connectiveCover R r.apex
  denominator := connectiveCoverInclusion R r.apex ≫ r.denominator
  numerator := connectiveCoverInclusion R r.apex ≫ r.numerator
  denominator_epi := by
    have := r.denominator_epi
    apply epi_of_epi_f
    intro n
    apply (ModuleCat.epi_iff_surjective _).2
    exact connectiveCoverInclusion_comp_surjective R r.denominator
      (fun j => (ModuleCat.epi_iff_surjective _).1 inferInstance) r.denominator_quasiIso n
  denominator_quasiIso := by
    have hA : IsConnective R A := by change A.X.IsLE 0; infer_instance
    have hc := r.apex_isConnective R hA
    change QuasiIso ((connectiveCoverInclusion R r.apex).hom ≫ r.denominator.hom)
    exact quasiIso_comp _ _ (hφ := connectiveCoverInclusion_quasiIso R r.apex hc)
      (hφ' := r.denominator_quasiIso)

lemma nonpositiveNormalization_apex : (nonpositiveNormalization R r).apex.X.IsStrictlyLE 0 :=
  coverComplex_nonpositive R r.apex

lemma nonpositiveNormalization_value {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L) :
    value R L hL (nonpositiveNormalization R r) = value R L hL r := by
  have := hL _ (nonpositiveNormalization R r).denominator_quasiIso
  have he : L.map (nonpositiveNormalization R r).denominator ≫ value R L hL r =
      L.map (nonpositiveNormalization R r).numerator := by
    change L.map (connectiveCoverInclusion R r.apex ≫ r.denominator) ≫ _ =
      L.map (connectiveCoverInclusion R r.apex ≫ r.numerator)
    rw [L.map_comp, L.map_comp, Category.assoc, denominator_value]
  apply (cancel_epi (L.map (nonpositiveNormalization R r).denominator)).1
  exact (denominator_value R L hL (nonpositiveNormalization R r)).trans he.symm

lemma nonpositiveNormalization_connectiveValue {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L) :
    connectiveValue R L hL (by change A.X.IsLE 0; infer_instance)
        (nonpositiveNormalization R r) =
      connectiveValue R L hL (by change A.X.IsLE 0; infer_instance) r := by
  have hA : IsConnective R A := by change A.X.IsLE 0; infer_instance
  have := hL ((nonpositiveNormalization R r).apex_isConnective R hA) hA _
    (nonpositiveNormalization R r).denominator_quasiIso
  have he : L.map (nonpositiveNormalization R r).denominator ≫ connectiveValue R L hL hA r =
      L.map (nonpositiveNormalization R r).numerator := by
    change L.map (connectiveCoverInclusion R r.apex ≫ r.denominator) ≫ _ =
      L.map (connectiveCoverInclusion R r.apex ≫ r.numerator)
    rw [L.map_comp, L.map_comp, Category.assoc, denominator_connectiveValue]
  apply (cancel_epi (L.map (nonpositiveNormalization R r).denominator)).1
  exact (denominator_connectiveValue R L hL hA (nonpositiveNormalization R r)).trans he.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
