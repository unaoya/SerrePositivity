module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Derived.DGFiniteOreRefinement

/-! # 二つの有限実屋根図式の共通係数 Ore 細分

概要：二つの実屋根図式を実閉分母上へ移し、第一の分子族を第二の分母へ同時に細分する。
方針：実 cofiltered over の共通 fiber 表示と有限係数の Ore 細分を接続する。
規約：元の二図式への全輸送と、細分後の全 Hom ホモトピーを保持する。
使われ方：四三角形を含む実屋根合成の高次パラメータ化の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable (r : K ⟶ dgRoofCorrespondence A D P x y)
variable (s : K ⟶ dgRoofCorrespondence A D P y z)

/-- 二つの元の実図式への輸送と、有限族の共通実 Ore 細分。 -/
structure DGFiniteRoofOreData where
  first : DGFiniteRoofPresentation A D P x y r
  second : DGFiniteRoofPresentation A D P y z s
  ore : DGFiniteOreRefinement A D P first.coefficient second.denominator.obj.hom

/-- 任意の有限な二つの実屋根図式に、全輸送を伴う共通実 Ore 細分が存在する。 -/
theorem dgFiniteRoofOreData_nonempty [IsDGPretriangulated A D] [K.Finite]
    (hP : DGQuotient.localKFlat A D P) : Nonempty (DGFiniteRoofOreData A D P x y z r s) := by
  obtain ⟨R⟩ := dgFiniteRoofPresentation_nonempty A D P x y r
  obtain ⟨S⟩ := dgFiniteRoofPresentation_nonempty A D P y z s
  obtain ⟨T⟩ := dgFiniteOreRefinement_nonempty A D P R.coefficient
    S.denominator.obj.hom hP S.denominator.property
  exact ⟨⟨R, S, T⟩⟩

end SerrePositivity.InfinityCategories
