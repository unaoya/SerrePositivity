module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalWeightedCone

/-!
概要：同じ普遍重み付き錐の全BE図式射に対する自然性。
方針：元の全frame族の対象表示と計算対象の反対表示を先に照合し、既存単位則を適用。
規約：IS-W2 R02の単位・自然性の証明分割。計算上限は変えない。
使われ方：指定native全錐族の標準点と全図式射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DiagramModel
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 全frame族の評価は元の同じ各図式のright frame。 -/
theorem strictBETotFrameDiagram_obj (F : K ⥤ (operad A).Algebra) :
    (rightFrameDiagramFamily A K).obj (op F) = rightFrameDiagram A K F := rfl

/-- 同じ計算対象の反対は、元の全frame族を同じ重みで実現した対象。 -/
theorem strictBETotFunctor_obj_op (F : K ⥤ (operad A).Algebra) :
    op ((framedLimitFunctor A K).obj F) =
      (FrameWeightRealization.functor Kᵒᵖ
        ((rightFrameDiagramFamily A K).obj (op F))).obj
          (HomotopyWeight.framedLimitWeight K) := rfl

/-- 元の全図式射による普遍錐の二つの像は、全重みの自然変換として等しい。 -/
theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((rightFrameDiagramFamily A K).map f.op).op).app
          (op ((framedLimitFunctor A K).obj F)) =
      strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K G)).map
          (((framedLimitFunctor A K).map f).op) := by
  have h := FrameWeightRealization.unit_frame_naturality Kᵒᵖ
    ((rightFrameDiagramFamily A K).map f.op) (HomotopyWeight.framedLimitWeight K)
  simpa only [strictBETotUniversalWeightedCone, strictBETotFunctor_map_op,
    strictBETotFunctor_obj_op, strictBETotFrameDiagram_obj] using h

end SerrePositivity.EInfinity.BarrattEccles
