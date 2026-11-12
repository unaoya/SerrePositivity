module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationStrictColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredLeftFibrationColimit

/-!
概要：通常の小さい filtered 図式の底上の余極限を、同じ left fibration の全余錐へ持ち上げる。
方針：通常の Over 余極限の left fibration 性を証明し、元の全脚をそのまま束ねる。
規約：元の図式と忘却後の指定余錐を厳密に保持する。
使われ方：任意の coherent filtered 余錐に比較する strict な余極限模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {B : SSet.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)

/-- 概要：元の strict filtered 図式の通常の底上の余極限余錐を持ち上げる。
方針：有限ホーンの filtered 持ち上げ性で余極限の left fibration 性を与える。
規約：余錐の全脚は元の Over 余極限の脚である。
使われ方：元の coherent 余錐と全関手同型で比較する strict 余錐。 -/
def filteredLeftFibrationCocone : Cocone F where
  pt := ⟨colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibration_of_filtered_isColimit _ _ (colimit.isColimit _) (fun i ↦ (F.obj i).property)⟩
  ι := {
    app i := colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B) i
    naturality _ _ f := colimit.w (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B) f }

/-- 概要：同じ strict filtered 全余錐は元の ∞ 圏で余極限である。
方針：忘却後の同じ通常の余極限を native 余錐の判定へ渡す。
規約：元の底は quasicategory、頂点も全脚も変更しない。
使われ方：任意の指定余錐へ保存性を戻す比較の入力。 -/
lemma filteredLeftFibrationCocone_isColimit [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (filteredLeftFibrationCocone F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationStrictCocone_isColimit _ (colimit.isColimit _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
