module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanPointedFiberTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan

/-!
概要：元の fiber の全 pointed 三角形を native 錐の三角形上の切断空間へ写す。
方針：同じ全持ち上げを native 図式の unstraightening へ持ち上げて curry する。
規約：全パラメータと全二単体を保持。使われ方：native 錐の切断による普遍性の適用。
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
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
  {K : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (k : K _⦋1⦌) (h : nativeConeTriangle c k = coherentTransformationPointTriangle T (ULift.up b))
/-- 元の小さい始域 fiber を native 錐の宇宙へ持ち上げたパラメータ。 -/
abbrev coherentNativeTriangleFiberParameters : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj
    (vertexFiber (smallLeftUnstraighteningProjection F) b)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b

/-- 元の全三角形を native な三角形図式の実際の unstraightening へ持ち上げる。 -/
def coherentNativeTriangleLift : (Δ[2] : SSet.{u + 1}) ⊗ a ⟶ leftUnstraightening D :=
  pullback.lift H (fst Δ[2] a)
    (coherentSmallFiberPointedTriangle_native_projection F G J x y T b c k h)

/-- 底は native 錐の三角形の恒等族。 -/
lemma coherentNativeTriangleLift_projection :
    coherentNativeTriangleLift F G J x y T b c k h ≫ leftUnstraighteningProjection D =
      fst Δ[2] a := pullback.lift_snd _ _ _

/-- 元の全 pointed 三角形が与える、native 三角形上の切断の全パラメータ族。 -/
def coherentNativeTriangleSections : a ⟶
    HomotopyLimits.simplicialSections (leftUnstraighteningProjection D) :=
  HomotopyLimits.simplicialSectionsLift (coherentNativeTriangleLift F G J x y T b c k h)
    (coherentNativeTriangleLift_projection F G J x y T b c k h)

/-- 普遍切断で評価して pointed 成分を取ると、同じ元の全三角形を厳密に回収する。 -/
lemma coherentNativeTriangleSections_evaluation_pointed :
    (Δ[2] ◁ coherentNativeTriangleSections F G J x y T b c k h) ≫
      HomotopyLimits.simplicialSectionsEvaluation (leftUnstraighteningProjection D) ≫
        pullback.fst pointedSpaceProjection D = H := by
  rw [← Category.assoc, coherentNativeTriangleSections,
    HomotopyLimits.simplicialSectionsLift_evaluation]
  exact pullback.lift_fst _ _ _

/-- 各辺でも、切断の評価は同じ元の三角形の辺の全円柱を回収する。 -/
lemma coherentNativeTriangleSections_face_pointed (i : Fin 3) :
    (stdSimplex.δ i ▷ a) ≫
      (Δ[2] ◁ coherentNativeTriangleSections F G J x y T b c k h) ≫
      HomotopyLimits.simplicialSectionsEvaluation (leftUnstraighteningProjection D) ≫
        pullback.fst pointedSpaceProjection D = (stdSimplex.δ i ▷ a) ≫ H := by
  rw [coherentNativeTriangleSections_evaluation_pointed]

end SerrePositivity.InfinityCategories.F2
