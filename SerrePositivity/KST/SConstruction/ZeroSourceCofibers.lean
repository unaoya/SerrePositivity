module
public import SerrePositivity.KST.SConstruction.FixedInitialArrows
public import SerrePositivity.KST.SConstruction.McCarthySpanEvaluations

/-! # subobject を指定零対象に固定した cofiber 図式
概要：cofiber 図式の subobject の strict fiber と、その標準 ι 型への比較の端点。
方針：始点評価の頂点 fiber を使い、quotient と固定始点の入力矢印を取り出す。
規約：零対象の別の選択へ置換しない。使われ方：第二の θ の大域的入力。
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

/-- 概要：subobject を指定零対象に厳密に固定した cofiber 図式の全空間。
方針：subobject 評価の頂点 fiber。
規約：高次単体でも subobject は定値。使われ方：θ の単一の coherent な入力空間。 -/
def zeroSourceCofibers {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (cofiberProjection C ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z.vertex

/-- 概要：固定零 subobject の図式を全 cofiber 図式へ含める。
方針：頂点 fiber の包含。
規約：元の正方形を保持。使われ方：θ の第一端点。 -/
def zeroSourceCofibersι {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibers z ⟶ cofiberDiagrams C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _

/-- 概要：固定零 subobject の図式の subobject は厳密に指定零対象。
方針：頂点 fiber の条件。
規約：全単体の等号。使われ方：固定始点の矢印への持ち上げ。 -/
lemma zeroSourceCofibersι_source {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibersι z ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const z.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：固定零 subobject の図式の quotient。
方針：正方形の (1,1) を評価する。
規約：元の quotient の選択を保持。使われ方：θ の第二端点。 -/
def zeroSourceCofibersQuotient {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) : zeroSourceCofibers z ⟶ C :=
  zeroSourceCofibersι z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1)

/-- 概要：元の入力矢印を固定始点の矢印の空間へ持ち上げる。
方針：subobject の厳密な等号を使う。
規約：入力矢印の全単体を変更しない。使われ方：θ の底の第一端点。 -/
def zeroSourceCofibersInput {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibers z ⟶ fixedSourceArrows z.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z.vertex
    (zeroSourceCofibersι z ≫ cofiberProjection C) (zeroSourceCofibersι_source z)

/-- 概要：固定始点の入力矢印を含めると元の cofiber の入力矢印。
方針：頂点 fiber の持ち上げの包含の式。
規約：全単体の等号。使われ方：cofiber 射影での θ の端点。 -/
lemma zeroSourceCofibersInput_ι {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibersInput z ≫ fixedSourceArrowsι z.vertex =
      zeroSourceCofibersι z ≫ cofiberProjection C := rfl

/-- 概要：同じ quotient の標準 ι 型の cofiber 図式。
方針：指定零対象からの標準 cofiber 関手を quotient に適用する。
規約：指定零対象を保持。使われ方：θ の第二端点。 -/
def zeroSourceCofibersCanonical {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibers z ⟶ cofiberDiagrams C :=
  zeroSourceCofibersQuotient z ≫ zeroCofiberFunctor z true

/-- 概要：標準 ι 型の図式も同じ subobject を持つ。
方針：標準 cofiber の入力始点の式。
規約：指定零対象への厳密な定値射。使われ方：第二端点の固定始点への持ち上げ。 -/
lemma zeroSourceCofibersCanonical_source {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibersCanonical z ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const z.vertex := by
  simp only [zeroSourceCofibersCanonical, Category.assoc]
  rw [zeroCofiberFunctor_input_evaluation]
  simp

/-- 概要：標準 ι 型の入力矢印を同じ固定始点の空間へ持ち上げる。
方針：標準 cofiber の入力始点の定値性。
規約：元の標準零射を保持。使われ方：θ の底の第二端点。 -/
def zeroSourceCofibersCanonicalInput {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibers z ⟶ fixedSourceArrows z.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z.vertex
    (zeroSourceCofibersCanonical z ≫ cofiberProjection C) (zeroSourceCofibersCanonical_source z)

/-- 概要：標準 ι 型の固定始点の矢印を含めると元の入力矢印。
方針：頂点 fiber の持ち上げの式。
規約：全単体の等号。使われ方：θ の底の第二端点の照合。 -/
lemma zeroSourceCofibersCanonicalInput_ι {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    zeroSourceCofibersCanonicalInput z ≫ fixedSourceArrowsι z.vertex =
      zeroSourceCofibersCanonical z ≫ cofiberProjection C := rfl

/-- 概要：元の cofiber 図式の middle から quotient への右辺の coherent な族。
方針：正方形の右辺で制限して uncurry する。
規約：元の右辺を保持。使われ方：θ の底の終点射の指定。 -/
def zeroSourceCofibersRightPrism {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    (Δ[1] : SSet.{u}) ⊗ zeroSourceCofibers z ⟶ C :=
  uncurry (zeroSourceCofibersι z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app C)

/-- 概要：右辺の族の始点は元の入力矢印の終点。
方針：下辺の終点と右辺の始点を同じ角で評価する。
規約：厳密等号。使われ方：θ の底の始点条件。 -/
lemma zeroSourceCofibersRightPrism_zero {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (zeroSourceCofibers z) ≫ zeroSourceCofibersRightPrism z =
      zeroSourceCofibersInput z ≫ fixedSourceArrowsTarget z.vertex := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, zeroSourceCofibersRightPrism, curry_uncurry]
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt,
    fixedSourceArrowsTarget]
  rw [← Category.assoc (zeroSourceCofibersInput z), zeroSourceCofibersInput_ι]
  rw [cofiberProjection, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：右辺の族の終点は同じ quotient の標準 ι 型の入力矢印の終点。
方針：右上角の評価と標準 ι 型の終点の式。
規約：厳密等号。使われ方：θ の底の終点条件。 -/
lemma zeroSourceCofibersRightPrism_one {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (zeroSourceCofibers z) ≫ zeroSourceCofibersRightPrism z =
      zeroSourceCofibersCanonicalInput z ≫ fixedSourceArrowsTarget z.vertex := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, zeroSourceCofibersRightPrism, curry_uncurry]
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt,
    fixedSourceArrowsTarget]
  rw [← Category.assoc (zeroSourceCofibersCanonicalInput z),
    zeroSourceCofibersCanonicalInput_ι]
  simp only [zeroSourceCofibersCanonical, Category.assoc]
  rw [zeroCofiberFunctor_input_evaluation]
  simp only [Fin.one_eq_zero_iff, Nat.reduceEqDiff]
  rfl

end SerrePositivity.KST.SConstruction
