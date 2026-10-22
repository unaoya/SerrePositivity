module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDiagramJointFibration
public import SerrePositivity.InfinityCategories.F2.Ind.UncurryGraphVertex
public import SerrePositivity.InfinityCategories.F1.PresheafUnstraightening

/-!
概要：共同評価の添字での制限は、元の coherent 前層図式の指定値そのもの。
方針：積の宇宙持ち上げと元のグラフを計算し、既存の小さい底変換同型を用いる。
規約：別の同値な前層への置換ではなく元の頂点を照合する。
使われ方：strict 化した各値と元の図式の unstraightening の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)

/-- 元の coherent 図式の指定添字での元の前層値。 -/
def presheafDiagramValue (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u} :=
  (presheafInfinityObjectEquiv C).symm (F.app _ (ULift.up (nerveVertex i)))

/-- 共同評価を同じ添字のグラフで制限すると、同じ元の前層を回収する。 -/
lemma presheafDiagramJointEvaluation_value (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map (underSectionFiberBase C.op i) ≫
      presheafDiagramJointEvaluation F = presheafDiagramValue F i := by
  have h : (SSet.uliftFunctor.{u + 1, u}).map (underSectionFiberBase C.op i) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op (nerve I)).hom =
      lift (𝟙 _) (SSet.const (ULift.up (nerveVertex i))) := rfl
  rw [presheafDiagramJointEvaluation, ← Category.assoc, h, uncurry_graph_vertex]
  rfl

/-- 元の共同 unstraightening の引き戻しは、元の前層値の同じ小さい復元と同型。 -/
def presheafDiagramJointValueIso (i : I) :
    smallLeftUnstraightening (presheafDiagramValue F i) ≅
      pullback (presheafDiagramJointProjection F) (underSectionFiberBase C.op i) :=
  (smallLeftUnstraighteningMap_isPullback (presheafDiagramValue F i)
    (presheafDiagramJointEvaluation F) (underSectionFiberBase C.op i)
    (presheafDiagramJointEvaluation_value F i)).isoPullback

/-- 同じ底変換同型の逆は、元の前層値の射影を厳密に保つ。 -/
lemma presheafDiagramJointValueIso_inv_projection (i : I) :
    (presheafDiagramJointValueIso F i).inv ≫
      smallLeftUnstraighteningProjection (presheafDiagramValue F i) =
        pullback.snd (presheafDiagramJointProjection F) (underSectionFiberBase C.op i) :=
  IsPullback.isoPullback_inv_snd _

end SerrePositivity.InfinityCategories.F2.Ind
