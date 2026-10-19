module

public import SerrePositivity.InfinityCategories.F1.PointedCylinderBaseFamily
public import SerrePositivity.InfinityCategories.F1.TransportSquareSpace

/-!
概要：円柱の prism 中間空間から実際の可換四角形の空間への射。
方針：pointed-space 値の族と分類図式の族の可換性を pushout の二部分で確認する。
規約：円柱の射影の left fibration 性は仮定しない。
使われ方：中間模型と実際の表現の族の比較の順方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱上の pointed-space 値の族は同じ分類区間の族を覆う。
方針：円柱部分では prism の底の式を、終点部分では fiber 条件を使う。
規約：全高次パラメーターでの厳密な可換性。
使われ方：関手空間の引き戻しへの持ち上げの可換条件。 -/
lemma pointedCylinderFamily_base {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFamily f s t ≫ pointedSpaceProjection =
      (mappingCylinderIntervalProjection f ▷ pointedCylinderPrismSpace f s t) ≫
        intervalMappingUncurry (pointedCylinderInterval f s t) := by
  apply parametrizedCylinder_hom_ext f
  · calc
      _ = pointedCylinderPrismEvaluation f s t ≫ pointedSpaceProjection := by
        rw [← Category.assoc]
        exact congrArg (fun w ↦ w ≫ pointedSpaceProjection)
          (parametrizedCylinderDesc_inl _ _ _ _)
      _ = (fst Δ[1] K ▷ pointedCylinderPrismSpace f s t) ≫
          intervalMappingUncurry (pointedCylinderInterval f s t) :=
        pointedCylinderPrismEvaluation_base f s t
      _ = _ := by
        rw [← Category.assoc, ← comp_whiskerRight, mappingCylinderIntervalProjection_inl]
  · calc
      _ = (uncurry (pointedCylinderPrismTarget f s t) ≫ vertexFiberι pointedSpaceProjection t) ≫
          pointedSpaceProjection := by
        rw [← Category.assoc]
        exact congrArg (fun w ↦ w ≫ pointedSpaceProjection)
          (parametrizedCylinderDesc_inr _ _ _ _)
      _ = SSet.const t := by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
      _ = (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ▷
          pointedCylinderPrismSpace f s t) ≫
            intervalMappingUncurry (pointedCylinderInterval f s t) := by
        change SSet.const t =
          (snd J _ ≫ prismEndpoint 1 _) ≫ intervalMappingUncurry (pointedCylinderInterval f s t)
        rw [Category.assoc, intervalMappingUncurry_one, SSet.comp_const]
      _ = _ := by
        rw [← Category.assoc, ← comp_whiskerRight, mappingCylinderIntervalProjection_inr]

/-- 概要：円柱上の関手空間の二成分は厳密に可換。
方針：族の底の等式を curry して前後合成の自然性を使う。
規約：図式側と全空間側を同時に保つ。
使われ方：実際の可換四角形の空間への射の定義。 -/
lemma pointedCylinderPointedMap_condition {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPointedMap f s t ≫
        (ihom (pushout (prismEndpoint 1 K) f)).map pointedSpaceProjection =
      pointedCylinderDiagram f s t ≫ (pre (mappingCylinderIntervalProjection f)).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  change uncurry (curry (pointedCylinderFamily f s t)) ≫ pointedSpaceProjection =
    (_ ▷ _) ≫ uncurry (curry (intervalMappingUncurry (pointedCylinderInterval f s t)))
  rw [uncurry_curry, uncurry_curry]
  exact pointedCylinderFamily_base f s t

/-- 概要：円柱の prism 中間空間から実際の可換四角形の空間への比較射。
方針：二つの族を関手空間の引き戻しへ持ち上げる。
規約：全高次単体を持つ実際の空間の射。
使われ方：表現条件を満たす頂点への制限と逆比較の構成。 -/
def pointedCylinderSquareMap {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismSpace f s t ⟶ transportSquareSpace (mappingCylinderIntervalProjection f) :=
  pullback.lift (pointedCylinderPointedMap f s t) (pointedCylinderDiagram f s t)
    (pointedCylinderPointedMap_condition f s t)

/-- 概要：比較射の全空間側は貼り合わせた関手の族。
方針：引き戻しの第一射影。
規約：射そのものの回収。
使われ方：逆比較の prism と終点の回収。 -/
lemma pointedCylinderSquareMap_pointed {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderSquareMap f s t ≫ transportSquarePointed (mappingCylinderIntervalProjection f) =
      pointedCylinderPointedMap f s t := pullback.lift_fst _ _ _

/-- 概要：比較射の底側は元の分類区間の族。
方針：引き戻しの第二射影。
規約：底の射も厳密に保持する。
使われ方：境界の分類図式を保つ比較。 -/
lemma pointedCylinderSquareMap_diagram {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderSquareMap f s t ≫ transportSquareDiagram (mappingCylinderIntervalProjection f) =
      pointedCylinderDiagram f s t := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
