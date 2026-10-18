module

public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapLifting
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：right fibration の写像空間と頂点 fiber を結ぶ比較の span。
方針：終点を固定した slice を底の頂点で fiber に制限し、slice の後合成と始点評価を使う。
規約：一方の射は自明 Kan fibration、他方は Kan fibration になる実際の射を構成する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の錐の pinched Hom と導来ファイバーの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：slice の後合成は可変頂点の射影と可換である。
方針：左包含との合成と Yoneda の後合成の式を使う。
規約：固定図式の始域 K は任意。
使われ方：Kerodon 7.4.1.6 の比較 span の底の整合条件。 -/
lemma sliceOverPostcomp_projection {K E B : SSet.{u}} (c : K ⟶ E) (r : E ⟶ B) :
    sliceOverPostcomp c r ≫ sliceOverProjection (c ≫ r) = sliceOverProjection c ≫ r := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl (stdSimplex.obj d.unop) K ≫ (s.val ≫ r)) =
    r.app d (SSet.yonedaEquiv (joinInl (stdSimplex.obj d.unop) K ≫ s.val))
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

/-- 概要：終点 c を持つ slice の、底の始点 x 上の単体集合。
方針：slice の始点射影と r の合成の頂点 fiber を取る。
規約：始点は E 内で固定せず、r による像 x だけを固定する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の写像空間の比較 span の中間空間。 -/
def rightFibrationMappingTotal {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) : SSet.{u} :=
  vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x

/-- 概要：比較の中間空間から底の終点 r(c) への写像空間の slice 模型への射。
方針：点上の slice の後合成を同じ底の始点 x で fiber に制限する。
規約：pinched Hom との既存の同型の前の slice fiber 表示を使う。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の比較 span の始域側の自明な射影。 -/
def rightFibrationMappingProjection {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    rightFibrationMappingTotal r c x ⟶
      vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm c ≫ r)) x :=
  vertexFiberMap (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r)
    (sliceOverProjection (SSet.yonedaEquiv.symm c ≫ r))
    (sliceOverPostcomp (SSet.yonedaEquiv.symm c) r)
    (sliceOverPostcomp_projection _ r) x

/-- 概要：比較の中間空間から底の頂点 x 上の元の fiber への始点評価。
方針：終点を固定した slice の始点射影を、r の頂点 fiber へ制限する。
規約：この射は可変な始点 d を記憶する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の比較の導来ファイバーの標的側。 -/
def rightFibrationMappingEvaluation {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    rightFibrationMappingTotal r c x ⟶ vertexFiber r x :=
  vertexFiberMap (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) r
    (sliceOverProjection (SSet.yonedaEquiv.symm c)) rfl x

/-- 概要：right fibration の写像空間の比較 span の射影は自明 Kan fibration。
方針：点上の slice の後合成の自明 Kan fibration 性を頂点 fiber へ移す。
規約：E と B の quasicategory 性は不要。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の比較の始域の同値な置換。 -/
instance rightFibrationMappingProjection_trivialKanFibration {E B : SSet.{u}}
    (r : E ⟶ B) [RightFibration r] (c : E.obj (Opposite.op ⦋0⦌))
    (x : B.obj (Opposite.op ⦋0⦌)) :
    TrivialKanFibration (rightFibrationMappingProjection r c x) := by
  have := sliceOverPostcomp_trivialKanFibration_of_rightFibration (SSet.yonedaEquiv.symm c) r
  exact vertexFiberMap_trivialKanFibration _ _ _ _ x

/-- 概要：right fibration の写像空間の比較 span の中間空間は Kan。
方針：底が quasicategory なら元の全空間も quasicategory とし、slice 射影との合成を使う。
規約：B の quasicategory 性だけを追加する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 のホモトピーファイバーの Kan 模型。 -/
instance rightFibrationMappingTotal_kanComplex {E B : SSet.{u}} [Quasicategory B]
    (r : E ⟶ B) [RightFibration r] (c : E.obj (Opposite.op ⦋0⦌))
    (x : B.obj (Opposite.op ⦋0⦌)) : KanComplex (rightFibrationMappingTotal r c x) := by
  have : Quasicategory E := quasicategory_of_innerFibration r
  have : RightFibration (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) :=
    ⟨rightFibrations.comp_mem _ _ RightFibration.mem RightFibration.mem⟩
  exact vertexFiber_kanComplex _ x

/-- 概要：right fibration の写像空間の比較 span の始点評価は Kan fibration。
方針：slice の始点射影から fiber の誘導射の right fibration 性を得て、両側の Kan 性を使う。
規約：r 自身の Kan fibration 性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の写像空間を strict fiber で検出する準備。 -/
instance rightFibrationMappingEvaluation_fibration {E B : SSet.{u}} [Quasicategory B]
    (r : E ⟶ B) [RightFibration r] (c : E.obj (Opposite.op ⦋0⦌))
    (x : B.obj (Opposite.op ⦋0⦌)) : Fibration (rightFibrationMappingEvaluation r c x) := by
  have : Quasicategory E := quasicategory_of_innerFibration r
  have := vertexFiber_kanComplex r x
  have : RightFibration (rightFibrationMappingEvaluation r c x) :=
    vertexFiberMap_rightFibration _ _ _ _ x
  exact rightFibration_fibration_of_kanComplex _

end SerrePositivity.InfinityCategories.HomotopyLimits
