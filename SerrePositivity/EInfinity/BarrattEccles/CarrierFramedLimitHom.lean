module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightFrames
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitProbe
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitCones
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameComparison

/-!
# 底の Kan 錐と忘却後の計算対象への導来 Hom

概要：BM 命題 4.1・Hovey §5.4 の同じ底の右 frame の錐を局所化 Hom と比較する。
方針：実際の複体の試験始域と重み付き実現の π₀ 比較を使う。
規約：元の計算対象の底を保持し、始域に cofibrancy を仮定しない。
使われ方：一般 homotopy 極限の忘却後の普遍性の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：図式全体に関手的な同じ底の右 frame（Hovey §5.2）。
方針：元の右 frame 図式族へ反対忘却を後合成する。
規約：元の図式射も同じ忘却像で移す。
使われ方：底の重み付き錐空間の図式自然性。 -/
def carrierRightFrameDiagramFamily :
    (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ Kᵒᵖ ⥤ SimplexCategory ⥤ (Complex A)ᵒᵖ :=
  rightFrameDiagramFamily A K ⋙ (Functor.whiskeringRight Kᵒᵖ _ _).obj
    ((Functor.whiskeringRight SimplexCategory _ _).obj (Operad.Algebra.forget (operad A)).op)
/-- 概要：任意の複体を試験始域とする底の右錐空間（Hovey §5.4）。
方針：同じ右 frame の底と具体的な複体の試験始域で重み付き Hom を取る。
規約：元の E 代数図式と実際の一点重みを保持する。
使われ方：元の複体から忘却後の計算対象への導来 Hom。 -/
def carrierFramedLimitConeSpace (Y : Complex A) : (K ⥤ (operad A).Algebra) ⥤ SSet.{u} :=
  (carrierRightFrameDiagramFamily A K).rightOp ⋙ FrameWeightRealization.homFamily Kᵒᵖ ⋙
    (CategoryTheory.evaluation (Complex A)ᵒᵖ (Kᵒᵖᵒᵖ ⥤ SSet.{u})).obj
      (op (carrierFramedLimitProbe A Y)) ⋙
    WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)

/-- 概要：底の右錐空間は実際の Kan 複体（Hovey §5.4）。
方針：底の frame の条件と具体的な試験始域の cofibrancy を代入する。
規約：元の複体に cofibrancy 条件はない。
使われ方：底の homotopy 極限比較を写像空間で検証する。 -/
lemma carrierFramedLimitConeSpace_kanComplex (F : K ⥤ (operad A).Algebra) (Y : Complex A) :
    SSet.KanComplex ((carrierFramedLimitConeSpace A K Y).obj F) := by
  let := projectiveModelCategory A
  have := carrierFramedLimitProbe_cofibrant A Y
  have : IsFibrant (op (carrierFramedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_kanComplex Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) (carrierRightFrameDiagram A K F)
    (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) f)
    (op (carrierFramedLimitProbe A Y))

/-- 概要：底の右錐の π₀ は元の複体から計算対象の底への局所化 Hom（Hovey §5.4）。
方針：反対圏の実現の π₀ 比較から試験始域を消し、同じ底の計算同型を使う。
規約：任意の非有界複体と元の framedLimitFunctor の底を値に取る。
使われ方：忘却後の一般導来極限の普遍性の Hom 側。 -/
def carrierFramedLimitHomPiZeroEquiv (F : K ⥤ (operad A).Algebra) (Y : Complex A) :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    SSet.π₀ ((carrierFramedLimitConeSpace A K Y).obj F) ≃
      (Q.obj Y ⟶ Q.obj ((framedLimitFunctor A K).obj F).carrier) := by
  let := projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := carrierFramedLimitProbe_cofibrant A Y
  have : IsFibrant (op (carrierFramedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (carrierRightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op
    (op (carrierFramedLimitProbe A Y))
  have : IsIso (Q.map ((carrierFramedLimitProbeComparison A).app Y)) :=
    Localization.inverts Q (weakEquivalences (Complex A)) _
      (carrierFramedLimitProbeComparison_quasiIso A Y)
  exact e.trans ((show
      (Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ (carrierRightFrameDiagram A K F)).obj
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶ Q.op.obj (op (carrierFramedLimitProbe A Y))) ≃
      (Q.obj (carrierFramedLimitProbe A Y) ⟶ Q.obj
        ((carrierWeightedCotensor A K F).obj (op (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)))) from
    { toFun := fun f => f.unop
      invFun := fun f => f.op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (Iso.homCongr (asIso (Q.map ((carrierFramedLimitProbeComparison A).app Y)))
      (Q.mapIso (framedLimitCarrierIso A K F).symm)))

end SerrePositivity.EInfinity.BarrattEccles
