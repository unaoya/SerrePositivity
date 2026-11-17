module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationCoefficientMap
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitHom

/-!
# 元の計算対象の底の同型の図式自然性

概要：BM 命題 4.1・Hovey §5.4 の同じ底の計算同型を図式に自然に束ねる。
方針：実際の実現の mate による係数射と Kan 拡張保存同型の自然性を照合する。
規約：元の計算対象・同型・図式射を保持する。
使われ方：底の導来 Hom の終域図式に関する自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：同じ底の右 frame の重み付き実現を図式の関手へ束ねる（Hovey §5.4）。
方針：同じ係数の族と実現の mate による射を合成する。
規約：元の一点重みと右 frame を保持する。
使われ方：底の計算同型の図式自然性。 -/
def carrierFramedLimitOpFunctor : (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ (Complex A)ᵒᵖ :=
  carrierRightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ ⋙
    (CategoryTheory.evaluation _ (Complex A)ᵒᵖ).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
/-- 概要：同じ底の右 frame の重み付き end の計算関手（Hovey §5.4）。
方針：反対圏で構成した関手を unop する。
規約：元の代数図式とその射の忘却を保持する。
使われ方：実際の計算対象の底との自然同型。 -/
def carrierFramedLimitFunctor : (K ⥤ (operad A).Algebra) ⥤ Complex A :=
  (carrierFramedLimitOpFunctor A K).unop
attribute [local irreducible] rightFrameFamily
attribute [local implicit_reducible] rightFrameDiagram rightFrameDiagramFamily
  carrierRightFrameDiagram carrierRightFrameDiagramFamily
set_option maxHeartbeats 400000 in
-- 具体的な frame の係数族と Kan 拡張の射の型照合が標準の上限を超えるため。
/-- 概要：実際の計算対象の底の同型は図式射に自然（Hovey §5.4）。
方針：元の mate の係数射を Kan 拡張の射と同定し保存同型の自然性を使う。
規約：既存の framedLimitCarrierIso の同じ成分を使う。
使われ方：底の導来 Hom 比較の終域自然性。 -/
lemma framedLimitCarrierIso_naturality {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ((framedLimitFunctor A K).map f).hom ≫ (framedLimitCarrierIso A K G).hom =
      (framedLimitCarrierIso A K F).hom ≫ (carrierFramedLimitFunctor A K).map f := by
  let U := Operad.Algebra.forget (operad A)
  have : U.IsRightAdjoint := (operad A).freeAlgebraAdjunction.isRightAdjoint
  let a : rightFrameDiagram A K G ⟶ rightFrameDiagram A K F :=
    (rightFrameDiagramFamily A K).map f.op
  have h := congr_app ((U.op.lanCompIsoOfPreserves uliftYoneda.{u,u,u}).inv.naturality
    (Functor.uncurry.map a))
      ((FrameWeightRealization.weightsEquivalence Kᵒᵖ).functor.obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K))
  have h' := congrArg (fun h => h.unop) h
  change U.map (((FrameWeightRealization.map Kᵒᵖ a).app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop) ≫
    (framedLimitCarrierIso A K G).hom =
    (framedLimitCarrierIso A K F).hom ≫
      ((FrameWeightRealization.map Kᵒᵖ (Functor.whiskerRight a
        ((Functor.whiskeringRight SimplexCategory _ _).obj U.op))).app
          (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationMap_eq_lan, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationMap_eq_lan]
  exact h'.symm

/-- 概要：元の計算関手の底と同じ底の重み付き end の自然同型（Hovey §5.4）。
方針：構成済みの各値の同型を証明した図式自然性で束ねる。
規約：元の framedLimitCarrierIso の同じ成分。
使われ方：底の局所化 Hom の後合成の照合。 -/
def framedLimitCarrierNatIso :
    framedLimitFunctor A K ⋙ Operad.Algebra.forget (operad A) ≅ carrierFramedLimitFunctor A K :=
  NatIso.ofComponents (framedLimitCarrierIso A K) (fun f => framedLimitCarrierIso_naturality A K f)

end SerrePositivity.EInfinity.BarrattEccles
