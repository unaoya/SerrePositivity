module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanNormalizedModelPathIso
public import SerrePositivity.InfinityCategories.F2.UliftHomotopyIsoDown

/-!
概要：正規化した実模型の全 path を持ち上げ、native 切断の同じ指定 path と比較する。
方針：二脚を元の実射へ明示して輸送し、下降の忠実性で指定値の等式を反映する。
規約：元の全円柱を保持。使われ方：元の模型から切断模型への二脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の二つの fiber 合成の間の、正規化した模型の同じ全 path 円柱。 -/
def coherentCospanNormalizedModelPathHomotopy : SSet.Homotopy (fl ≫ ql) (fr ≫ qr) := by
  let H := functorHomotopyPrecomp (intervalPullbackPathHomotopy ql qr) n
  refine { h := H.h, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change _ = fl ≫ ql
    exact H.h₀.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ ql) (coherentCospanNormalizedModelFiberComparison_left F X Y Z C b)))
  · change _ = fr ≫ qr
    exact H.h₁.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ qr) (coherentCospanNormalizedModelFiberComparison_right F X Y Z C b)))
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 元の全円柱から読む同型は、正規化した実模型の元の指定同型そのもの。 -/
lemma coherentCospanNormalizedModelPathIso_eq_homotopy :
    coherentCospanNormalizedModelPathIso F X Y Z C b =
      functorIsoOfSimplicialHomotopy (coherentCospanNormalizedModelPathHomotopy F X Y Z C b) := by
  unfold coherentCospanNormalizedModelPathIso
  apply functorIsoOfEq_of_homotopy_h_eq
    (functorHomotopyPrecomp (intervalPullbackPathHomotopy ql qr) n)
    (coherentCospanNormalizedModelPathHomotopy F X Y Z C b)
  · rw [functorIso_precomp_hom, intervalPullbackPathIso_hom]
    exact (functorHomotopyPrecomp_hom (intervalPullbackPathHomotopy ql qr) n).symm
  · rfl
  · rfl

/-- 正規化した実模型の全 path の持ち上げは、元の native 切断の指定 path に厳密に一致。 -/
lemma coherentCospanNormalizedModelPathLiftIso_eq_section :
    functorIsoOfSimplicialHomotopy (uliftSimplicialHomotopy.{u, u + 1}
      (coherentCospanNormalizedModelPathHomotopy F X Y Z C b)) =
        coherentCospanNativeSectionFiberPathIso F X Y Z C b := by
  apply functorIsoDown_injective
  dsimp only
  rw [functorIsoDown_uliftHomotopy, ← coherentCospanNormalizedModelPathIso_eq_homotopy,
    coherentCospanNormalizedModelPathIso_eq_section_down]
  rfl

end SerrePositivity.InfinityCategories.F2
