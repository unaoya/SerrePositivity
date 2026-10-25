module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorAlgebraDiagonalHom
public import SerrePositivity.KST.SConstruction.DGOdotVerdierInput
public import SerrePositivity.KST.SConstruction.PerfectDGFullyFaithful
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugationLaws
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful
/-!
概要：Milnor 比較から元小 Perf 対角と固定 ν の充満忠実性へ進む生成入力を分離する。
方針：自由対象の Hom 準同型性を D-17 の入力へ渡し、同じ元対角を保持する。
規約：生成判定は明示入力であり、Milnor 条件だけからの無条件完成とはしない。
使われ方：D-17 の公開供給を代入する前の、元二射の Verdier 列の組み立てに用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
/-- 自由対象の実対角から、元の小 Perf 対角への生成判定の供給境界。 -/
def DGGluingMilnorSmallPerfectGeneration : Prop :=
  HomQuasiIso (dgGluingMilnorAlgebraDiagonal R d) →
    HomQuasiIso (dgOdotQuotientInput R d).diagonal
lemma dgGluingMilnorSmallPerfectDiagonal_homQuasiIso
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    HomQuasiIso (dgOdotQuotientInput R d).diagonal :=
  hgen (dgGluingMilnorAlgebraDiagonal_homQuasiIso R d h)
lemma dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    IsFullyFaithful (dgNerve.map (dgOdotQuotientInput R d).diagonal) :=
  dgNerve_map_isFullyFaithful_of_quasiIso _
    (dgGluingMilnorSmallPerfectDiagonal_homQuasiIso R d h hgen)
lemma dgGluingMilnorDiagonalInput_homQuasiIso
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    HomQuasiIso (dgOdotDiagonalInputMap R d).down := by
  intro x y
  exact dgGluingMilnorSmallPerfectDiagonal_homQuasiIso R d h hgen x.label.down y.label.down
lemma dgGluingMilnorDiagonalExactMap_isFullyFaithful
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    IsFullyFaithful (dgOdotDiagonalExactMap R d).hom := by
  rw [dgOdotDiagonalExactMap, dgKInputNuMap_eq]
  change IsFullyFaithful (dgNerve.map (presentedPerfectDGAction R _ _
    (dgOdotDiagonalInputMap R d).down))
  apply dgNerve_map_isFullyFaithful_of_quasiIso
  intro X Y
  rw [presentedPerfectDGAction_map]
  let := perfectDGExtension_homQuasiIso_of_homQuasiIso R _ _
    (dgOdotDiagonalInputMap R d).down (dgGluingMilnorDiagonalInput_homQuasiIso R d h hgen)
      (presentedPerfectDGValue R _ X) (presentedPerfectDGValue R _ Y)
  change QuasiIso (_ ≫ (enrichedClosedIsoHomIso (Complex R)
    (presentedPerfectDGActionIso R _ _ (dgOdotDiagonalInputMap R d).down X)
    (presentedPerfectDGActionIso R _ _ (dgOdotDiagonalInputMap R d).down Y)).hom)
  infer_instance
end SerrePositivity.InfinityCategories
