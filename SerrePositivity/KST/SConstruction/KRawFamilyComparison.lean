module
public import SerrePositivity.KST.SConstruction.KRelativeFamilyLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-! # 同じ raw 射影を持つ BF 族の境界固定比較
概要：同じ raw 族を持ち上げた二つの BF 族を、共通境界を固定して実ホモトピーで比較する。
方針：元の射影の全単射 RLP を、境界固定の鉛直ホモトピー構成へ適用する。
規約：全区間の raw 射影と境界の定数性を保持する。成分の一致だけでは適用しない。
使われ方：直接延長と入れ子の延長における BF の選択の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.SimplicialModel.MonoRightLiftingRelativeHomotopy
open scoped Simplicial
variable (X Y : StableModel.{u}) {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (a b : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  (hp : a ≫ kRawMappingProjection X Y = b ≫ kRawMappingProjection X Y)
  (hj : j ≫ a = j ≫ b)

/-- 同じ実 raw 射影と共通境界を持つ BF 族の境界固定実比較。 -/
def kRawFamilyComparison : SSet.Homotopy a b :=
  (exists_relative_vertical_homotopy
    (kRawMappingProjection X Y) (kRawMappingProjection_rlp X Y) j a b hp hj).choose

/-- 比較円柱の全時刻の raw 射影は元の同じ族で定数。 -/
lemma kRawFamilyComparison_projection :
    (kRawFamilyComparison X Y j a b hp hj).h ≫ kRawMappingProjection X Y =
      fst U (Δ[1] : SSet.{u}) ≫ a ≫ kRawMappingProjection X Y :=
  (exists_relative_vertical_homotopy
    (kRawMappingProjection X Y) (kRawMappingProjection_rlp X Y) j a b hp hj).choose_spec.1

/-- 比較円柱は指定した共通境界上で同じ BF 族に厳密に固定される。 -/
lemma kRawFamilyComparison_boundary :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (kRawFamilyComparison X Y j a b hp hj).h =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ a :=
  (exists_relative_vertical_homotopy
    (kRawMappingProjection X Y) (kRawMappingProjection_rlp X Y) j a b hp hj).choose_spec.2

/-- 境界に既存の比較円柱を指定しても、同じ全 raw 射影を保つ実比較を構成する。 -/
def kPrescribedRawFamilyComparisonData
    (A : SSet.Homotopy (j ≫ a) (j ≫ b))
    (hA : A.h ≫ kRawMappingProjection X Y =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ a ≫ kRawMappingProjection X Y) :
    {H : SSet.Homotopy a b //
      H.h ≫ kRawMappingProjection X Y =
        fst U (Δ[1] : SSet.{u}) ≫ a ≫ kRawMappingProjection X Y ∧
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = A.h} := by
  let hex := exists_vertical_homotopy
    (kRawMappingProjection X Y) (kRawMappingProjection_rlp X Y) a b hp
  have ha : A.h ≫ kRawMappingProjection X Y =
      (j ▷ (Δ[1] : SSet.{u})) ≫ hex.choose.h ≫ kRawMappingProjection X Y := by
    rw [hex.choose_spec, whiskerRight_fst_assoc]
    exact hA
  let hext := exists_extension (kRawMappingProjection X Y)
    (kRawMappingProjection_rlp X Y) j hex.choose A ha
  exact ⟨hext.choose, hext.choose_spec.1.trans hex.choose_spec, hext.choose_spec.2⟩

/-- 指定した比較の全時刻でも raw 射影は同じ族に固定される。 -/
lemma kPrescribedRawFamilyComparisonData_projection
    (A : SSet.Homotopy (j ≫ a) (j ≫ b))
    (hA : A.h ≫ kRawMappingProjection X Y =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ a ≫ kRawMappingProjection X Y) :
    (kPrescribedRawFamilyComparisonData X Y j a b hp A hA).val.h ≫
        kRawMappingProjection X Y =
      fst U (Δ[1] : SSet.{u}) ≫ a ≫ kRawMappingProjection X Y :=
  (kPrescribedRawFamilyComparisonData X Y j a b hp A hA).property.1

/-- 比較は境界上で、指定した同じ実比較円柱を全時刻で回収する。 -/
lemma kPrescribedRawFamilyComparisonData_boundary
    (A : SSet.Homotopy (j ≫ a) (j ≫ b))
    (hA : A.h ≫ kRawMappingProjection X Y =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ a ≫ kRawMappingProjection X Y) :
    (j ▷ (Δ[1] : SSet.{u})) ≫
        (kPrescribedRawFamilyComparisonData X Y j a b hp A hA).val.h = A.h :=
  (kPrescribedRawFamilyComparisonData X Y j a b hp A hA).property.2

end SerrePositivity.KST.SConstruction
