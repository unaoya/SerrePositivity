module

public import SerrePositivity.InfinityCategories.F1.PullbackTransport
public import SerrePositivity.InfinityCategories.F1.DirectKanUnstraighteningTransport

/-!
概要：strict な Kan 値図式の係数の射を、普遍 pointed-space 射影の transport と比較する。
方針：直接復元比較の fiber 射を引き戻しの fiber 同型で移し、transport の底変換公式を合成する。
規約：値域 𝒮 は coherent nerve による SpaceInfinity。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の作用の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：Kan 図式の値から、coherent 表示の頂点における普遍射影の fiber への比較射。
方針：直接復元比較の fiber 射と引き戻しの fiber 同型を合成する。
規約：元の値の単体集合を u+1 に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6、普遍射影の transport と係数の射の比較の両端。 -/
noncomputable def kanDiagramUniversalFiberComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (F.obj c).obj ⟶
      vertexFiber pointedSpaceProjection
        ((kanDiagramCoherentNerve F).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c))) :=
  directKanUnstraighteningFiberComparison F c ≫
    (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom

/-- 概要：各係数値と普遍射影の対応する fiber の比較射は同値。
方針：直接復元比較の fiber 同値と引き戻しの fiber 同型を合成する。
規約：選択した比較射そのものの同値性を述べる。
使われ方：Kerodon Corollary 5.6.0.6、普遍射影の作用を値の同値を介して調べる。 -/
lemma kanDiagramUniversalFiberComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    IsQCatEquivalence (kanDiagramUniversalFiberComparison F c) :=
  (directKanUnstraighteningFiberComparison_isQCatEquivalence F c).comp
    (qCatEquivalenceOfIso
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F)
        (ULift.up (nerveVertex c)))).isQCatEquivalence

/-- 概要：普遍射影の transport は strict な図式の係数の射と値の同値を介して関手同型まで可換。
方針：直接復元比較の transport 同型と底の引き戻しの transport 同型を合成する。
規約：辺は持ち上げた nerve の f の辺を coherent 表示で写したもの。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の射への作用の同定。 -/
noncomputable def kanDiagramUniversalFiberComparison_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫ kanDiagramUniversalFiberComparison F d)
      (kanDiagramUniversalFiberComparison F c ≫ edgeTransport pointedSpaceProjection
        (SSet.Edge.map (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)) (kanDiagramCoherentNerve F))) := by
  have e₀ := FunctorIso.postcomp (directKanUnstraighteningFiberComparison_transportIso F f)
    (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex d))).hom
  have e₁ := FunctorIso.precomp
    (edgeTransport_pullbackIso pointedSpaceProjection (kanDiagramCoherentNerve F)
      (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)))
    (kanDiagramUniversalFiberComparison F c)
  change FunctorIso
    (directKanUnstraighteningFiberComparison F c ≫
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).inv ≫
      edgeTransport (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)) ≫
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex d))).hom)
    (kanDiagramUniversalFiberComparison F c ≫ _) at e₁
  simp only [Iso.hom_inv_id_assoc] at e₁
  simp only [Category.assoc] at e₀
  exact e₀ ≪≫ e₁

/-- 概要：図式の辺の像に沿う普遍射影の transport の同値性は係数の射の同値性と一致する。
方針：引き戻しの transport の判定を直接復元の係数の判定へ合成する。
規約：係数の射の同値性は元の宇宙で述べる。
使われ方：Kerodon Corollary 5.6.0.6、普遍射影の作用による同値性の検出。 -/
lemma kanDiagramUniversalTransport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport pointedSpaceProjection
      (SSet.Edge.map (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)) (kanDiagramCoherentNerve F))) ↔
      IsQCatEquivalence (F.map f) :=
  (edgeTransport_pullback_isQCatEquivalence_iff pointedSpaceProjection (kanDiagramCoherentNerve F)
    (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f))).symm.trans
      (directKanUnstraighteningTransport_isQCatEquivalence_iff F f)

end SerrePositivity.InfinityCategories
