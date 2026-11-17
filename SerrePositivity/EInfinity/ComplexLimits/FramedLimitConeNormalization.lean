module

public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitMixedClasses
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeReindexPoints

/-!
# 元の通常錐の類と右錐の添字比較

概要：Hovey §5.4 の両 frame の錐比較を元の通常錐の類で正規化する。
方針：添字移送の類の計算と既存の混合 Hom の一致を合成する。
規約：元の試験始域・右 frame・通常錐を保持する。
使われ方：同じ coneToFramedLimit の局所化像の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右錐の添字同型は元の通常錐の類を保つ（Hovey §5.4）。
方針：元の添字移送の逆と同じ反対射同型による後合成を計算する。
規約：元の framedLimitConeClass と同じ零単体を使う。
使われ方：両 frame の比較の全体の正規化。 -/
lemma rightSimplicialConeIso_coneClass (F : K ⥤ (Complex A)) (c : Cone F) :
    SSet.mapπ₀ (rightSimplicialConeIso A K c.pt F).hom
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (strictSimplicialConeFamily A K F c)) = framedLimitConeClass A K F c := by
  let e := opOpEquivalence K
  let W := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K
  let G := rightSimplicialHomDiagram A K c.pt F
  let s := strictSimplicialConeFamily A K F c
  let i := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso e W).app G
  let j := rightSimplicialHomDiagramIso A K c.pt F
  have h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso_class e W s
  have hi : SSet.mapπ₀ i.inv (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (e.functor ⋙ W) (Functor.whiskerLeft e.functor s) := by
    change SSet.mapπ₀ i.hom _ = _ at h
    rw [← h, ← SSet.mapπ₀_comp_apply, Iso.hom_inv_id, SSet.mapπ₀_id_apply]
  change SSet.mapπ₀ (i.inv ≫ (WeightedCones.coneSpace Kᵒᵖᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).map j.hom) _ = _
  rw [SSet.mapπ₀_comp_apply, hi]
  have hm := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass_map Kᵒᵖᵒᵖ (e.functor ⋙ W)
    (Functor.whiskerLeft e.functor s) j.hom
  refine hm.trans ?_
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (e.functor ⋙ W) _ =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (e.functor ⋙ W) _
  congr 1

/-- 概要：両錐比較は元の通常錐の類そのものを結ぶ（Hovey §5.4）。
方針：混合 Hom 内の族の一致と右錐の添字移送の計算を合成する。
規約：同じ試験始域の比較を前置した元の錐の射を使う。
使われ方：局所化 Hom の同値が通常錐からの比較を保つ証明。 -/
lemma sourceRightConeComparisonIso_coneClass (F : K ⥤ (Complex A)) (c : Cone F) :
    let f : (Functor.const K).obj (framedLimitProbe A c.pt) ⟶ F :=
      (Functor.const K).map (framedLimitProbeComparison A c.pt) ≫ c.π
    (sourceRightConeComparisonIso A K c.pt F SSet.π₀Functor
        SimplicialModel.PiZeroLocalization.inverts_anodyne).hom
      (BarrattEccles.CarrierDiagram.constantDiagramSourceClass A K f) = framedLimitConeClass A K F
        c := by
  exact (sourceRightConeComparisonIso_strictClass A K F c).trans
    (rightSimplicialConeIso_coneClass A K F c)

end SerrePositivity.EInfinity.ComplexLimits
