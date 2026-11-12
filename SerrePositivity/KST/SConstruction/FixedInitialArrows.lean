module
public import SerrePositivity.KST.SConstruction.RelativeInitialPrism
public import SerrePositivity.KST.SConstruction.ArCofiberFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-! # 始点を指定始対象に固定した矢印の空間
概要：始点を一つの始対象に厳密に固定した矢印の終点射影は trivial Kan fibration。
方針：境界上の矢印の族を固定始点の相対 prism 延長で埋める。
規約：元の矢印全体を保つ。使われ方：第二の θ の subobject を厳密に固定する比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：始点を指定頂点に厳密に固定した全矢印。
方針：始点評価の頂点 fiber を取る。
規約：始対象性はここでは不要。使われ方：零 subobject を固定した自然変換の入力。 -/
def fixedSourceArrows {C : SSet.{u}} (z : C _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z

/-- 概要：固定始点の矢印を元の矢印の関手空間へ含める。
方針：頂点 fiber の包含。
規約：全ての高次単体を保持。使われ方：cofiber 射影との接続。 -/
def fixedSourceArrowsι {C : SSet.{u}} (z : C _⦋0⦌) :
    fixedSourceArrows z ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z

/-- 概要：固定始点の矢印の終点を評価する射。
方針：包含と終点評価を合成する。
規約：始点の条件は維持する。使われ方：右辺を指定した比較の持ち上げ。 -/
def fixedSourceArrowsTarget {C : SSet.{u}} (z : C _⦋0⦌) : fixedSourceArrows z ⟶ C :=
  fixedSourceArrowsι z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：固定始点の矢印の族の始点は指定頂点で厳密に一定。
方針：頂点 fiber の包含の合成則。
規約：全単体の等号。使われ方：cofiber の subobject の固定。 -/
lemma fixedSourceArrowsι_source {C : SSet.{u}} (z : C _⦋0⦌) :
    fixedSourceArrowsι z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.const z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：指定始対象を始点に持つ矢印の終点射影は全境界を持ち上げる。
方針：始点・終点と既存の境界上の矢印を保持する相対 prism の延長。
規約：零次元を含み、モデル構造の仮定は不要。使われ方：第二の θ の coherent な比較。 -/
lemma fixedSourceArrowsTarget_trivialKanFibration {C : SSet.{u}} (z : C _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let H := uncurry (a ≫ fixedSourceArrowsι z)
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary n : SSet.{u}) ≫ H = SSet.const z := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry, Category.assoc,
      fixedSourceArrowsι_source, SSet.comp_const]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary n : SSet.{u}) ≫ H = (boundary n).ι ≫ b := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact sq.w
  obtain ⟨F, hF, hF₀, hF₁⟩ := exists_relative_initialPrism z hz (boundary n) b H h₀ h₁
  have hs : curry F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.const z := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₀]
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z
    (curry F) hs
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) z
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF
  · change curry F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₁]

end SerrePositivity.KST.SConstruction
