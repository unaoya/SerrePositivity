module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareColimitCone

/-!
概要：整合する四角形の族を底と全空間の余極限へ貼り合わせる。
方針：二つの内部 Hom の極限で図式を貼り、全空間の内部 Hom の極限で可換性を判定する。
規約：全高次パラメーターの族を扱う。
使われ方：四角形空間の余極限に沿う降下の普遍射。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：整合する四角形の族の全空間側の図式を貼り合わせる。
方針：全空間の余極限の内部 Hom の極限へ持ち上げる。
規約：錐のパラメーターを保持する。
使われ方：貼り合わせた四角形の第一成分。 -/
def transportSquareColimitPointedLift {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.leftFunc.mapCocone c)) (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    s.pt ⟶ (ihom c.pt.left).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePointedCone_isLimit c hc).lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareConePointed s)

/-- 概要：整合する四角形の族の分類図式を貼り合わせる。
方針：底の余極限の内部 Hom の極限へ持ち上げる。
規約：錐のパラメーターを保持する。
使われ方：貼り合わせた四角形の第二成分。 -/
def transportSquareColimitDiagramLift {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.rightFunc.mapCocone c)) (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    s.pt ⟶ (ihom c.pt.right).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareDiagramCone_isLimit c hc).lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareConeDiagram s)

/-- 概要：貼り合わせた全空間側の図式は指定した各項を厳密に回収する。
方針：内部 Hom の極限の lift の脚公式。
規約：全高次パラメーターでの等式。
使われ方：四角形の貼り合わせの制限公式。 -/
lemma transportSquareColimitPointedLift_fac {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.leftFunc.mapCocone c)) (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor))
    (j : J) :
    transportSquareColimitPointedLift c hc s ≫ (pre (c.ι.app j).left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity =
      s.π.app (Opposite.op j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (D.obj j).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePointedCone_isLimit c hc).fac (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareConePointed s) (Opposite.op j)

/-- 概要：貼り合わせた分類図式は指定した各項を厳密に回収する。
方針：内部 Hom の極限の lift の脚公式。
規約：全高次パラメーターでの等式。
使われ方：底側の貼り合わせの制限公式。 -/
lemma transportSquareColimitDiagramLift_fac {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.rightFunc.mapCocone c)) (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor))
    (j : J) :
    transportSquareColimitDiagramLift c hc s ≫ (pre (c.ι.app j).right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity =
      s.π.app (Opposite.op j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (D.obj j).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareDiagramCone_isLimit c hc).fac (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareConeDiagram s) (Opposite.op j)

/-- 概要：二つの貼り合わせた図式は元の射影と厳密な可換四角形を成す。
方針：全空間の余極限の内部 Hom の極限の全脚で可換性を検査する。
規約：分類図式と全空間側の射をともに固定する。
使われ方：整合する四角形を実際の大域的な四角形へ束ねる。 -/
lemma transportSquareColimitLift_condition {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    transportSquareColimitPointedLift c hcE s ≫ (ihom c.pt.left).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      transportSquareColimitDiagramLift c hcB s ≫ (pre c.pt.hom).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := by
  let h := isLimitOfPreserves ((internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) hcE.op
  apply h.hom_ext
  intro j
  change (transportSquareColimitPointedLift c hcE s ≫ (ihom c.pt.left).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) ≫
      (pre (c.ι.app j.unop).left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity =
    (transportSquareColimitDiagramLift c hcB s ≫ (pre c.pt.hom).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) ≫
      (pre (c.ι.app j.unop).left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  have hw : (c.ι.app j.unop).left ≫ c.pt.hom =
      (D.obj j.unop).hom ≫ (c.ι.app j.unop).right := (c.ι.app j.unop).w
  rw [Category.assoc, ← pre_comm_ihom_map, ← Category.assoc,
    transportSquareColimitPointedLift_fac]
  simp only [Category.assoc]
  rw [← NatTrans.comp_app, ← pre_map, hw, pre_map, NatTrans.comp_app,
    ← Category.assoc (transportSquareColimitDiagramLift c hcB s),
    transportSquareColimitDiagramLift_fac]
  simpa only [Category.assoc] using congrArg (fun f ↦ s.π.app j ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition (D.obj j.unop).hom)

/-- 概要：整合する四角形の族を余極限上の四角形の族へ貼り合わせる。
方針：二つの貼り合わせた図式と検証した可換性を引き戻しへ束ねる。
規約：錐の全高次パラメーターを保持する。
使われ方：四角形空間の降下の極限の lift。 -/
def transportSquareColimitLift {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) : s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace c.pt.hom :=
  pullback.lift (transportSquareColimitPointedLift c hcE s)
    (transportSquareColimitDiagramLift c hcB s) (transportSquareColimitLift_condition c hcE hcB s)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
