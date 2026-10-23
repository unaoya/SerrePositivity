module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomComponentPullback
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：元の全 Hom の分類作用を、一成分を固定した実際の fiber の写像に制限する。
方針：同じ評価の可換性で fiber に持ち上げ、同じ底への比較の fiber と厳密に結ぶ。
規約：fiber の比較の全空間への合成は、元の分類作用のまま。
使われ方：一次元の分類 Hom 作用の同値性を fiber ごとに検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C)
local notation "s" => (cocartesianHomSourceComponent F G c)
local notation "e" => (coherentHomIntervalComparison
  (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c))
local notation "t" => (cocartesianHomIntervalEvaluation F G c)

/-- 一成分を固定した元の Hom の作用は、同じ評価 fiber の間の実際の写像を誘導する。 -/
def cocartesianHomFixedComponentComparison
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    vertexFiber s b ⟶ vertexFiber t ((e).app _ b) :=
  vertexFiberLift t ((e).app _ b)
    (vertexFiberι s b ≫ cocartesianTransportDiagramHomInterval F G) (by
      have h : cocartesianTransportDiagramHomInterval F G ≫ t = s ≫ e :=
        cocartesianTransportDiagramHomInterval_evaluation F G c
      rw [Category.assoc, h, ← Category.assoc, vertexFiberι_comp, SSet.const_comp])

/-- 同じ固定成分の比較を全空間に含めると、元の全 Hom 作用を回収する。 -/
lemma cocartesianHomFixedComponentComparison_ι
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    cocartesianHomFixedComponentComparison F G c b ≫ vertexFiberι t ((e).app _ b) =
      vertexFiberι s b ≫ cocartesianTransportDiagramHomInterval F G := rfl

/-- 同じ底への比較の fiber を標準同型で移すと、元の作用の固定成分比較そのもの。 -/
lemma cocartesianHomComponentComparison_fiber
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    vertexFiberMap s (pullback.snd t e) (cocartesianHomComponentComparison F G c)
      (cocartesianHomComponentComparison_snd F G c) b ≫
        (vertexFiberPullbackIso t e b).hom =
      cocartesianHomFixedComponentComparison F G c b := by
  apply vertexFiber_hom_ext t ((e).app _ b)
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc, vertexFiberMap_ι,
    Category.assoc, cocartesianHomComponentComparison_fst]
  rfl

end SerrePositivity.InfinityCategories
