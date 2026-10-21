module

public import SerrePositivity.InfinityCategories.F2.NativePointedConeLift
public import SerrePositivity.InfinityCategories.F2.CoherentNativeTriangleSections

/-!
概要：元の各点の cospan 錐全体を、実際の始域 fiber の族上で pointed に持ち上げる。
方針：縮小前の元の始点族を錐頂点上に照合し、全錐の始点固定延長を適用する。
規約：元の全錐・全 fiber・始点を保持。使われ方：左右二三角形の共通の全錐との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b

/-- 元の小さい fiber の全点を縮小前の同じ pointed 始点へ送る族。 -/
def coherentCospanFiberPointedSource : a ⟶ PointedSpaceInfinity.{u} :=
  (m).left ≫ pullback.fst pointedSpaceProjection F

/-- 元の始点族の底は元の native 錐の頂点である。 -/
lemma coherentCospanFiberPointedSource_projection :
    coherentCospanFiberPointedSource F b ≫ pointedSpaceProjection = SSet.const (c).vertex := by
  rw [coherentCospanFiberPointedSource, Category.assoc, pullback.condition,
    ← Category.assoc]
  change ((m).left ≫ leftUnstraighteningProjection F) ≫ F = _
  rw [smallFiberSourceRestriction_projection, SSet.const_comp,
    coherentCospanConePointwiseCone_vertex]

/-- 同じ全 native 錐と元の fiber の始点族を持つ pointed な全持ち上げ。 -/
def coherentCospanPointedConeLift :
    join (Δ[0] : SSet.{u + 1}) (horn 2 2 : SSet.{u + 1}) ⊗ a ⟶ PointedSpaceInfinity.{u} :=
  nativePointedConeLift c (coherentCospanFiberPointedSource F b)
    (coherentCospanFiberPointedSource_projection F X Y Z C b)

/-- 底は元の各点の native 錐の全図式である。 -/
lemma coherentCospanPointedConeLift_projection :
    coherentCospanPointedConeLift F X Y Z C b ≫ pointedSpaceProjection =
      fst (join Δ[0] (horn 2 2)) a ≫ (c).val :=
  nativePointedConeLift_projection c _ _

/-- 錐の頂点では、元の全 fiber の同じ始点族を厳密に回収する。 -/
lemma coherentCospanPointedConeLift_initial :
    (joinInl Δ[0] (horn 2 2) ▷ a) ≫ coherentCospanPointedConeLift F X Y Z C b =
      snd Δ[0] a ≫ coherentCospanFiberPointedSource F b :=
  nativePointedConeLift_initial c _ _

end SerrePositivity.InfinityCategories.F2
