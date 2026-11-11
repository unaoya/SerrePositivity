module

public import SerrePositivity.KST.Spectra.PointedParametricPost
public import SerrePositivity.KST.Spectra.PointedIhomParameterExchange

/-!
概要：全パラメータ後合成を、元の族の転置への後合成と内部 Hom の交換で表示する。
方針：同じ ihomParameterAction の評価式を恒等入力で用い、転置を二度戻す。
規約：族を頂点ごとに分解しない。使われ方：普遍区間の源側の実辺と全族作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 全族後合成は、同じ転置した族への mapping と同じ源交換の合成に厳密一致する。 -/
lemma parametricPost_exchange (A : PointedSimplicialSet.{u})
    {P Z Z' : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom Z Z') :
    parametricPost A v = PointedObject.basedHomMap A (transpose v) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z').hom := by
  have hid : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 (PointedObject.basedHom A Z))
      (PointedObject.basedHom A Z') = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact congrArg (fun m => m.app (PointedObject.basedHom A Z'))
      (MonoidalClosed.pre_id (PointedObject.basedHom A Z))
  have h := transpose_ihomParameterAction v (𝟙 (PointedObject.basedHom A Z))
  change transpose (𝟙 (PointedObject.basedHom A Z) ≫
    PointedObject.basedHomMap A (transpose v) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z').hom) =
      (v ≫ ihomAction A Z Z') ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 (PointedObject.basedHom A Z))
        (PointedObject.basedHom A Z') at h
  rw [Category.id_comp, hid, Category.comp_id] at h
  have ht := congrArg transpose h
  rw [transpose_transpose] at ht
  exact ht.symm

end SerrePositivity.KST.Spectra.PointedMapping
