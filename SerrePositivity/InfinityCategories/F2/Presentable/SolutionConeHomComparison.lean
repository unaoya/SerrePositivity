module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeClassificationHom
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallSolutionCone
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseUnstraightening

/-!
概要：小さい全解錐を、元の制限関手から頂点の共変 Hom への全自然な射に送る。
方針：元の全解の底の錐を分類し、元の関手との宇宙変更比較を合成する。
規約：同じ解錐の頂点と全図式を使い、保存性の追加仮定は要求しない。
使われ方：余表現可能性の retract を構成する順射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
  (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (F : C ⟶ SpaceInfinity.{u})

/-- 概要：小さい全解の分類図式は元の関手の同じ宇宙変更と全自然同型。
方針：元の縮小同型を分類し、unstraightening の宇宙変更比較を続ける。
規約：同型の対象は元の i への制限そのもの。
使われ方：小さい解錐の幾何的比較を元の関手へ戻す。 -/
def smallSolutionClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection (i ≫ F))))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (i ≫ F) ≫ Compact.spaceUniverseDiagram) :=
  Compact.leftClassification_overIso _ _ (smallLeftUnstraighteningIso (i ≫ F))
    (smallLeftUnstraighteningIso_projection (i ≫ F)) ≪≫
      Compact.spaceUniverseUnstraightening_classificationIso (i ≫ F)

/-- 概要：全解錐は元の小さい解図式の底の全錐を与える。
方針：元の錐の全射へ全空間の射影を後合成する。
規約：元の底の図式を厳密に保持する。
使われ方：分類による Hom 比較の幾何的な錐。 -/
def smallSolutionBaseCone (d : JoinCone (smallSolutionLift i F)) :
    JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection (i ≫ F)) ≫ i) :=
  ⟨d.val ≫ leftUnstraighteningProjection F, by
    rw [← Category.assoc, d.property, smallSolutionLift_projection]
    rfl⟩

/-- 概要：底の解錐の頂点は元の全解頂点の像。
方針：同じ全射を持つ後合成錐との頂点の一致を読む。
規約：指定した d の頂点を保持する。
使われ方：得られた表現可能 Hom の表現対象の照合。 -/
lemma smallSolutionBaseCone_vertex (d : JoinCone (smallSolutionLift i F)) :
    (smallSolutionBaseCone i F d).vertex =
      (leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex := by
  exact mapJoinCone_vertex (leftUnstraighteningProjection F) d

/-- 概要：全解錐から元の制限関手の宇宙変更を頂点の全共変 Hom へ写す。
方針：底の錐を分類し、同じ全解の分類同型の逆を前合成する。
規約：元の全関手圏の射を構成し、対象ごとの射の族に弱めない。
使われ方：accessible 関手の余表現可能性を導く retract の射。 -/
def solutionConeHomComparison (d : JoinCone (smallSolutionLift i F)) :
    FunctorHom ((SSet.uliftFunctor.{u + 2, u + 1}).map (i ≫ F) ≫ Compact.spaceUniverseDiagram)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map i ≫ covariantRepresentableInfinity
        ((leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex)) := by
  have h := coneClassificationHom
    ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection (i ≫ F))) i
    (smallSolutionBaseCone i F d)
  rw [smallSolutionBaseCone_vertex] at h
  exact (smallSolutionClassificationIso i F).inv ≫ h

end SerrePositivity.InfinityCategories.F2.Presentable
