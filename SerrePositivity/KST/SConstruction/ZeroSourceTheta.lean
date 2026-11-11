module
public import SerrePositivity.KST.SConstruction.ZeroSourceCofibers
public import SerrePositivity.KST.SConstruction.TrivialFibrationPrism

/-! # 指定零 subobject を固定する θ の大域的 prism
概要：零 subobject の cofiber 図式から同じ quotient の標準 ι 型へ coherent な prism を作る。
方針：固定始点の矢印の終点射影で右辺を持ち上げ、cofiber 射影で両端を保って持ち上げる。
規約：subobject を全時刻で厳密に固定する。使われ方：McCarthy の第二のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の右辺を保ち、指定零始点の入力矢印同士を結ぶ prism。
方針：始対象からの矢印の終点射影の自明ファイブレーションで持ち上げる。
規約：始点は高次単体でも厳密に一定。使われ方：θ の cofiber 射影での像。 -/
def zeroSourceThetaInput {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    (Δ[1] : SSet.{u}) ⊗ zeroSourceCofibers z ⟶ fixedSourceArrows z.vertex := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z.vertex) :=
    fixedSourceArrowsTarget_trivialKanFibration z.vertex z.isInitial
  exact liftPrismOfTrivialKanFibration (fixedSourceArrowsTarget z.vertex)
    (zeroSourceCofibersInput z) (zeroSourceCofibersCanonicalInput z)
    (zeroSourceCofibersRightPrism z) (zeroSourceCofibersRightPrism_zero z)
      (zeroSourceCofibersRightPrism_one z)

/-- 概要：入力矢印の θ の始点は元の入力矢印。
方針：両端指定持ち上げの始点の式。
規約：厳密等号。使われ方：cofiber 図式の第一端点。 -/
lemma zeroSourceThetaInput_zero {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (zeroSourceCofibers z) ≫ zeroSourceThetaInput z =
      zeroSourceCofibersInput z := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z.vertex) :=
    fixedSourceArrowsTarget_trivialKanFibration z.vertex z.isInitial
  unfold zeroSourceThetaInput
  exact liftPrismOfTrivialKanFibration_zero _ _ _ _ _ _

/-- 概要：入力矢印の θ の終点は標準 ι 型の入力矢印。
方針：両端指定持ち上げの終点の式。
規約：厳密等号。使われ方：cofiber 図式の第二端点。 -/
lemma zeroSourceThetaInput_one {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (zeroSourceCofibers z) ≫ zeroSourceThetaInput z =
      zeroSourceCofibersCanonicalInput z := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z.vertex) :=
    fixedSourceArrowsTarget_trivialKanFibration z.vertex z.isInitial
  unfold zeroSourceThetaInput
  exact liftPrismOfTrivialKanFibration_one _ _ _ _ _ _

/-- 概要：入力矢印の θ の終点評価は元の cofiber 図式の右辺。
方針：持ち上げの射影の式。
規約：元の右辺の全単体を保つ。使われ方：θ の点ごとの可逆性。 -/
lemma zeroSourceThetaInput_target {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceThetaInput z ≫ fixedSourceArrowsTarget z.vertex =
      zeroSourceCofibersRightPrism z := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z.vertex) :=
    fixedSourceArrowsTarget_trivialKanFibration z.vertex z.isInitial
  unfold zeroSourceThetaInput
  exact liftPrismOfTrivialKanFibration_projection _ _ _ _ _ _

private lemma thetaInput_start {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (zeroSourceCofibers z) ≫
      (zeroSourceThetaInput z ≫ fixedSourceArrowsι z.vertex) =
        zeroSourceCofibersι z ≫ cofiberProjection C := by
  rw [← Category.assoc, zeroSourceThetaInput_zero, zeroSourceCofibersInput_ι]

private lemma thetaInput_end {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (zeroSourceCofibers z) ≫
      (zeroSourceThetaInput z ≫ fixedSourceArrowsι z.vertex) =
        zeroSourceCofibersCanonical z ≫ cofiberProjection C := by
  rw [← Category.assoc, zeroSourceThetaInput_one, zeroSourceCofibersCanonicalInput_ι]

/-- 概要：指定零 subobject を固定して元の cofiber 図式を標準 ι 型へ動かす prism。
方針：cofiber 射影の自明ファイブレーションで両端を指定して持ち上げる。
規約：固定零 subobject の全空間上の一つの選択。使われ方：θ の単体的自然性。 -/
def zeroSourceTheta {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    (Δ[1] : SSet.{u}) ⊗ zeroSourceCofibers z ⟶ cofiberDiagrams C :=
  liftPrismOfTrivialKanFibration (cofiberProjection C) (zeroSourceCofibersι z)
    (zeroSourceCofibersCanonical z) (zeroSourceThetaInput z ≫ fixedSourceArrowsι z.vertex)
      (by exact thetaInput_start z) (by exact thetaInput_end z)

/-- 概要：θ の始点は元の固定零 subobject の図式。
方針：両端指定持ち上げの始点の式。
規約：正方形全体の厳密回収。使われ方：ρ の終端との照合。 -/
lemma zeroSourceTheta_zero {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (zeroSourceCofibers z) ≫ zeroSourceTheta z = zeroSourceCofibersι z :=
  liftPrismOfTrivialKanFibration_zero _ _ _ _ _ _

/-- 概要：θ の終点は同じ quotient の標準 ι 型の図式。
方針：両端指定持ち上げの終点の式。
規約：正方形全体の厳密回収。使われ方：切断と quotient の合成との照合。 -/
lemma zeroSourceTheta_one {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (zeroSourceCofibers z) ≫ zeroSourceTheta z = zeroSourceCofibersCanonical z :=
  liftPrismOfTrivialKanFibration_one _ _ _ _ _ _

/-- 概要：θ の cofiber 射影は固定始点の入力矢印の prism。
方針：持ち上げの射影の式。
規約：全単体での厳密等号。使われ方：subobject の固定と可逆性の反映。 -/
lemma zeroSourceTheta_projection {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceTheta z ≫ cofiberProjection C =
      zeroSourceThetaInput z ≫ fixedSourceArrowsι z.vertex :=
  liftPrismOfTrivialKanFibration_projection _ _ _ _ _ _

/-- 概要：θ の全時刻で subobject は指定零対象に厳密に固定される。
方針：cofiber 射影と固定始点の矢印の条件を使う。
規約：高次単体でも定値。使われ方：左 fiber 内の第二ホモトピー。 -/
lemma zeroSourceTheta_source {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceTheta z ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const z.vertex := by
  rw [← Category.assoc, zeroSourceTheta_projection, Category.assoc,
    fixedSourceArrowsι_source, SSet.comp_const]

end SerrePositivity.KST.SConstruction
