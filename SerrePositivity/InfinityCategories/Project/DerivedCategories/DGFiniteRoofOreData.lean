module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreRefinement

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
variable (s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z)

/-- 二つの元の実図式への輸送と、有限族の共通実 Ore 細分。 -/
structure DGFiniteRoofOreData where
  first : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation A D P x y r
  second : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation A D P y z s
  ore : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreRefinement A D P first.coefficient second.denominator.obj.hom

/-- 任意の有限な二つの実屋根図式に、全輸送を伴う共通実 Ore 細分が存在する。 -/
theorem dgFiniteRoofOreData_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite]
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) : Nonempty (DGFiniteRoofOreData A D P x y z r s) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofPresentation_nonempty A D P x y r
  obtain ⟨S⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofPresentation_nonempty A D P y z s
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteOreRefinement_nonempty A D P R.coefficient
    S.denominator.obj.hom hP S.denominator.property
  exact ⟨⟨R, S, T⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
