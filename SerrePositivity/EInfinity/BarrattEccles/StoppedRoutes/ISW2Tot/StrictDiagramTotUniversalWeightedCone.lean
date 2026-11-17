module
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightUnitNaturality

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE endの普遍重み付き錐と、その全図式射への自然性を指定する。
方針：既存FrameWeightRealizationの随伴の単位を、元の同じ重みで読む。
規約：IS-W2 R02・R03の単位・自然性の法則。native錐の構成は別工程。
使われ方：指定native錐の標準脚・全単体を追跡する元データ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.DiagramModel
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 元の同じ計算対象の恒等射が表す、普遍重み付き右frame錐。 -/
def strictBETotUniversalWeightedCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).obj
        (op ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)) :=
  (FrameWeightRealization.adjunction Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).unit.app
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)

/-- 同じ随伴同値で戻すと、普遍錐は元の同じendの恒等射。 -/
theorem strictBETotUniversalWeightedCone_identity (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((FrameWeightRealization.adjunction Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).homEquiv
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (op ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).symm
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone A K F) = 𝟙 _ := by
  apply ((FrameWeightRealization.adjunction Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).homEquiv
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (op ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).injective
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- 任意の元の射が表す重み付き錐は、同じ普遍錐への前合成そのもの。 -/
theorem strictBETotUniversalWeightedCone_precomp (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (f : Y ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) Y) f =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone A K F ≫
        (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).map f.op := by
  change (FrameWeightRealization.adjunction Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).homEquiv
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op Y) f.op = _
  rw [Adjunction.homEquiv_unit]
  rfl

/-- 元の全frame族の同じ図式射を、各frameの間の射として読む。 -/
def strictBETotFrameMap {F G : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K G ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).map f.op

/-- 全frame族での評価と同じ射であり、別の比較射を選ばない。 -/
theorem strictBETotFrameMap_eq {F G : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameMap A K f = (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).map f.op := rfl

/-- 元の全計算関手の射は同じ重み付き実現のmateそのもの。 -/
theorem strictBETotFunctor_map_op {F G : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).map f).op =
      (FrameWeightRealization.map Kᵒᵖ ((_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).map f.op)).app
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) := rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
