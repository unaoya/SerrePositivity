module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanDiagramExtension

/-!
概要：両端の重みを固定し、中央の anodyne な射だけに沿って cospan の自然変換を延長する。
方針：中央は Kan 充填、両端は重みの同型からの持ち上げで自然性を保つ。
規約：係数図式の両脚の fibration 性は不要。使われ方：loop の区間重みと三角形重みの比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra


/-- 両端の重みが同型なら、中央の Kan 充填を元の cospan の自然変換へ延長できる。 -/
lemma exists_cospan_extension_of_central_anodyne
    {A B H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B)
    [IsIso (j.app (AsSmall.up.obj .left))] [IsIso (j.app (AsSmall.up.obj .right))]
    (hj : anodyneExtensions (j.app (AsSmall.up.obj .one)))
    [KanComplex (H.obj (AsSmall.up.obj .one))] (a : A ⟶ H) :
    ∃ b : B ⟶ H, j ≫ b = a := by
  have centerLift : HasLiftingProperty (j.app (AsSmall.up.obj .one))
      (terminal.from (H.obj (AsSmall.up.obj .one))) :=
    hj _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  let sq : CommSq (a.app (AsSmall.up.obj .one)) (j.app (AsSmall.up.obj .one))
      (terminal.from (H.obj (AsSmall.up.obj .one)))
      (terminal.from (B.obj (AsSmall.up.obj .one))) := ⟨terminal.hom_ext _ _⟩
  obtain ⟨b, hb, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_cospan_diagram_extension j a sq.lift sq.fac_left
  exact ⟨b, hb⟩

end SerrePositivity.KST.Spectra
