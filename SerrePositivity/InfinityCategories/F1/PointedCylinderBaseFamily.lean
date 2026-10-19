module

public import SerrePositivity.InfinityCategories.F1.PointedCylinderFamily
public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinderIntervalExtension

/-!
概要：円柱の中間空間の区間の分類図式と prism の底の等式。
方針：元の全 lift 空間の区間パラメーターを回収して展開する。
規約：始点と終点は指定した s,t に厳密に固定する。
使われ方：貼り合わせた円柱の族が同じ底の族を覆うことの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱の中間空間の底の区間パラメーター。
方針：元の lift 空間の射影から区間成分を取る。
規約：係数の射影は忘れる。
使われ方：円柱上の表現の分類図式の族。 -/
def pointedCylinderInterval {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismSpace f s t ⟶ intervalMappingSpace s t :=
  pointedCylinderPrismLift f s t ≫ pointedPrismLiftParameters K s t ≫ snd _ _

/-- 概要：円柱の中間空間の区間からの分類図式の族。
方針：両端固定の区間の族を展開して curry する。
規約：底の図式の全高次パラメーターを保持する。
使われ方：transport square の底側の成分。 -/
def pointedCylinderDiagram {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismSpace f s t ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj SpaceInfinity.{u} :=
  curry (intervalMappingUncurry (pointedCylinderInterval f s t))

/-- 概要：prism の評価の底は底の区間の族を係数を忘れて評価したもの。
方針：全 lift の底の公式を引き戻し、区間の展開の自然性を使う。
規約：区間と係数を第一因子にまとめる。
使われ方：円柱部分での可換四角形の確認。 -/
lemma pointedCylinderPrismEvaluation_base {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismEvaluation f s t ≫ pointedSpaceProjection =
      (fst (Δ[1] : SSet.{u + 1}) K ▷ pointedCylinderPrismSpace f s t) ≫
        intervalMappingUncurry (pointedCylinderInterval f s t) := by
  let P := pointedCylinderPrismLift f s t
  let H := prismLiftSpacePrism pointedSpaceProjection K (pointedPrismData K s t)
  have hb : H ≫ pointedSpaceProjection = (Δ[1] ◁ snd K (pointedPrismLiftSpace K s t)) ≫
      intervalMappingUncurry (pointedPrismLiftParameters K s t ≫ snd _ _) :=
    pointedPrismEvaluation_base K s t
  calc
    _ = (α_ Δ[1] K _).hom ≫ (Δ[1] ◁ (K ◁ P)) ≫ H ≫ pointedSpaceProjection := by
      dsimp only [pointedCylinderPrismEvaluation]
      rw [uncurry_natural_left]
      rfl
    _ = (α_ Δ[1] K _).hom ≫ (Δ[1] ◁ (K ◁ P)) ≫
        (Δ[1] ◁ snd K (pointedPrismLiftSpace K s t)) ≫
          intervalMappingUncurry (pointedPrismLiftParameters K s t ≫ snd _ _) := by rw [hb]
    _ = _ := by
      dsimp only [pointedCylinderInterval]
      rw [intervalMappingUncurry_precomp]
      rfl

end SerrePositivity.InfinityCategories
