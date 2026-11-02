module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelLeftCorrectionHomotopy

/-!
概要：実模型の左脚を厳密化した指定同型の共通終点像は、native 切断の元の指定 path。
方針：元の全補正円柱の像と、持ち上げた正規化模型 path の指定値の等式を合成する。
規約：同じ指定同型を使用。使われ方：native な左右の二脚の共通終点での貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local notation "a" => coherentCospanModelLeftCorrectionParameter F X Y Z C b
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : HomotopicalAlgebra.Fibration f :=
  relativeCospanLeftTarget_fibration pointedSpaceProjection d

/-- 元の実模型の左脚の厳密化に使った、同じ全 path の指定同型の制限。 -/
def coherentCospanModelLeftCorrectionIso :=
  (liftedIntervalCospanLeftIso ql f ((η).app WalkingCospan.left)
    ((η).app WalkingCospan.one) ((η).naturality WalkingCospan.Hom.inl)).precomp a

/-- この同じ補正同型の共通点像は、元の native 切断の指定 path と型付きで一致する。 -/
lemma coherentCospanModelLeftCorrectionIso_image :
    HEq (((coherentCospanModelLeftCorrectionIso F X Y Z C b).postcomp f).postcomp (I).hom)
      (coherentCospanNativeSectionFiberPathIso F X Y Z C b) := by
  have h : ((coherentCospanModelLeftCorrectionIso F X Y Z C b).postcomp f).postcomp (I).hom =
      functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp
        (functorHomotopyPostcomp (coherentCospanModelLeftCorrectionHomotopy F X Y Z C b) f)
          (I).hom) := by
    unfold coherentCospanModelLeftCorrectionIso liftedIntervalCospanLeftIso
    rw [kanHomotopyRectificationIso, ← homotopyIso_precomp,
      ← homotopyIso_postcomp, ← homotopyIso_postcomp]
    rfl
  have ht := homotopyIso_heq_of_h_eq
    (functorHomotopyPostcomp
      (functorHomotopyPostcomp (coherentCospanModelLeftCorrectionHomotopy F X Y Z C b) f)
        (I).hom)
    (uliftSimplicialHomotopy.{u, u + 1}
      (coherentCospanNormalizedModelPathHomotopy F X Y Z C b))
    ((Category.assoc _ _ _).trans (coherentCospanModelLeftCorrectionHomotopy_image F X Y Z C b))
  exact (heq_of_eq h).trans
    (ht.trans (heq_of_eq (coherentCospanNormalizedModelPathLiftIso_eq_section F X Y Z C b)))

end SerrePositivity.InfinityCategories.F2
