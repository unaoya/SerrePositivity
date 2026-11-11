module

public import SerrePositivity.KST.Spectra.PointedParametricPostExchange

/-!
概要：元の随伴への全族後合成を転置し、同じ uncurry への前合成と反復 curry で表示する。
方針：証明済みのパラメータ評価作用の式を同じ射の族へ適用する。
規約：Kan 性や区間選択不要。使われ方：保存済み Kan 随伴自然性の実入力への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ随伴への全族作用の転置は、元の評価への前合成と同じ二重 curry。 -/
lemma transpose_pre_parametricPost {P K A E V : PointedSimplicialSet.{u}}
    (q : A ⟶ PointedObject.basedHom K E) (v : P ⟶ PointedObject.basedHom E V) :
    transpose (q ≫ parametricPost K v) =
      (v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (uncurry q) V) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K A V).hom := by
  have he : q ≫ parametricPost K v =
      (q ≫ PointedObject.basedHomMap K (transpose v)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K P V).hom := by
    rw [parametricPost_exchange, Category.assoc]
  have ht := (congrArg transpose he).trans (transpose_ihomParameterAction v q)
  have hc := congrArg (v ≫ ·) (ihomParameterAction_eq_adjoint_pre (V := V) q)
  exact ht.trans (by simpa only [Category.assoc] using hc)

end SerrePositivity.KST.Spectra.PointedMapping
