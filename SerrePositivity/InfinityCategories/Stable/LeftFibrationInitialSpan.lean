module
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapLifting
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CoslicePinchedLeft
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberKan

/-! # 始対象を持つ left fibration の表現可能な比較 span

概要：left fibration の fiber と底の写像空間を、始対象下の coslice の fiber で結ぶ。
方針：始点を固定した coslice の後合成と終点射影を同じ基底の fiber に制限する。
規約：二つの射は始対象性の下で自明 Kan fibration。使われ方：余極限の Hom による表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定始点から出る全空間の辺の、底の終点 y を固定した空間。
方針：点下の coslice の終点射影と p の合成の fiber を取る。
規約：全空間での終点は固定しない。使われ方：表現可能な比較の中間空間。 -/
def leftFibrationInitialTotal {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (y : B _⦋0⦌) : SSet.{u} :=
  vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ p) y

/-- 概要：中間空間から元の left fibration の fiber への終点評価。
方針：coslice の終点射影を底の y 上へ制限する。
規約：始点 c は全空間の実際の頂点。使われ方：余錐空間への比較。 -/
def leftFibrationInitialEvaluation {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (y : B _⦋0⦌) : leftFibrationInitialTotal p c y ⟶ vertexFiber p y :=
  vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ p) p
    (sliceUnderProjection (SSet.yonedaEquiv.symm c)) rfl y

/-- 概要：中間空間から底の c の像から y への coslice fiber への射影。
方針：点下の coslice の後合成を同じ底の y 上へ制限する。
規約：写像空間の左模型への同型の前の表示。使われ方：Hom との比較。 -/
def leftFibrationInitialProjection {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (y : B _⦋0⦌) : leftFibrationInitialTotal p c y ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y :=
  vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ p)
    (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p))
    (sliceUnderPostcomp (SSet.yonedaEquiv.symm c) p) (sliceUnderPostcomp_projection _ _) y

/-- 概要：底の写像空間側への射影は自明 Kan fibration。
方針：left fibration の点下の後合成の自明性を頂点 fiber に移す。
規約：底と全空間の quasicategory 性は不要。使われ方：比較 span の第一の同値。 -/
instance leftFibrationInitialProjection_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (y : B _⦋0⦌) :
    TrivialKanFibration (leftFibrationInitialProjection p c y) := by
  have := sliceUnderPostcomp_trivialKanFibration (SSet.yonedaEquiv.symm c) p
  exact HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ y

/-- 概要：始点 c が始対象なら元の fiber 側への評価も自明 Kan fibration。
方針：始対象の coslice 射影の自明性を頂点 fiber に移す。
規約：p 自体の充填性を要求しない。使われ方：比較 span の第二の同値。 -/
lemma leftFibrationInitialEvaluation_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌) :
    TrivialKanFibration (leftFibrationInitialEvaluation p c y) := by
  have := (isInitialVertex_iff_trivialKanFibration c).1 hc
  exact HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ y

/-- 概要：底が quasicategory の left fibration の比較の中間空間は Kan 複体。
方針：点下の coslice 射影との合成を left fibration として fiber の Kan 性を使う。
規約：始点の始対象性は不要。使われ方：比較 span の連結成分への移行。 -/
instance leftFibrationInitialTotal_kanComplex {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (y : B _⦋0⦌) :
    KanComplex (leftFibrationInitialTotal p c y) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : LeftFibration (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ p) :=
    ⟨leftFibrations.comp_mem _ _ LeftFibration.mem LeftFibration.mem⟩
  exact vertexFiber_kanComplex_of_leftFibration _ _

/-- 概要：底の coslice fiber は c の像から y への左 pinched 写像空間と同型。
方針：点図式の後合成の Yoneda 表示を同定し、既存の左模型の同型を使う。
規約：p の充填性は不要。使われ方：比較 span を通常の Hom へ結ぶ。 -/
def leftFibrationInitialBaseIso {E B : SSet.{u}} (p : E ⟶ B) (c : E _⦋0⦌)
    (y : B _⦋0⦌) : vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y ≅
      pinchedHomLeft (p.app (Opposite.op ⦋0⦌) c) y :=
  eqToIso (congrArg (fun q => vertexFiber (sliceUnderProjection q) y)
    (SSet.yonedaEquiv_symm_comp c p)) ≪≫
      (pinchedLeftCosliceFiberIso (p.app (Opposite.op ⦋0⦌) c) y).symm

end SerrePositivity.InfinityCategories
