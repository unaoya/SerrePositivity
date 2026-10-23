module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNormalizedModelFiberComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeSectionPathDownComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackPathClass

/-!
概要：入力 fiber を正規化した実模型の指定 path は、同じ native 切断の指定 path の下降。
方針：元の全 path の厳密な一致を使い、両端を元の二つの fiber 合成へ明示して輸送する。
規約：元の指定値を保持。使われ方：大宇宙の二脚の底の整合への等式の反映。
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
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "ql" => vertexFiberMap pX pZ cf
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ cg
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local notation "m" => coherentCospanConeTotalModelFiberComparison F X Y Z C b
local notation "fb" => vertexFiberMap (cf ≫ pZ) pZ cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ pZ) pZ cg rfl b
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の正規化した比較の指定 path を、元の実際の二つの fiber 合成で表した同型。 -/
def coherentCospanNormalizedModelPathIso : FunctorIso (fl ≫ ql) (fr ≫ qr) :=
  functorIsoOfEq ((intervalPullbackPathIso ql qr).precomp n)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ ql) (coherentCospanNormalizedModelFiberComparison_left F X Y Z C b)))
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ qr) (coherentCospanNormalizedModelFiberComparison_right F X Y Z C b)))

/-- 正規化後も、元の同じ native 切断の指定 path の下降と厳密に一致する。 -/
lemma coherentCospanNormalizedModelPathIso_eq_section_down :
    coherentCospanNormalizedModelPathIso F X Y Z C b =
      coherentCospanNativeSectionFiberPathDownIso F X Y Z C b := by
  have hn := intervalPullbackPathIso_precomp_heq_of_path_eq ql qr fb gb n m
    (coherentCospanNormalizedModelFiberComparison_path F X Y Z C b)
  have ho : HEq ((intervalPullbackPathIso fb gb).precomp m)
      (coherentCospanNativeSectionFiberPathDownIso F X Y Z C b) := by
    have he := functorIsoOfEq_heq ((intervalPullbackPathIso fb gb).precomp m)
      (coherentCospanConeFiberComparisonPath_left F X Y Z C b)
      (coherentCospanConeFiberComparisonPath_right F X Y Z C b)
    exact he.symm.trans
      ((heq_of_eq (coherentCospanModelFiberPathIso_eq_native F X Y Z C b)).trans
        (coherentCospanNativeSectionFiberPathDownIso_heq_native F X Y Z C b).symm)
  unfold coherentCospanNormalizedModelPathIso
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans (hn.trans ho))

end SerrePositivity.InfinityCategories.F2
