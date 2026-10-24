module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductSmallFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCommonFiberProductVertexIso
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy

/-!
概要：元の有限 coherent 積の小さい全空間から元の共通 fiber 積への指定比較は同値。
方針：元の各 fiber 比較を有限積表示と厳密に照合し、left fibration の fiber 判定を使う。
規約：底の quasicategory 性は不要。元の比較射・全射影・底を保持する。
使われ方：sifted 余極限と全有限積の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の有限族が left fibration なら、元の共通 fiber 積の底射影も left fibration。 -/
lemma finiteCommonFiberProductBase_leftFibration (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (hp : ∀ i, LeftFibration (p i)) :
    LeftFibration (pullback.snd (nonemptyFiniteSSetProductMap n p)
      (nonemptyFiniteDiagonal B n)) := by
  have : LeftFibration (nonemptyFiniteSSetProductMap n p) :=
    nonemptyFiniteSSetProductMap_leftFibration n p hp
  exact ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    nonemptyFiniteSSetProductMap n p))⟩

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    LeftFibration (pullback.snd (nonemptyFiniteSSetProductMap n
      (fun i ↦ smallLeftUnstraighteningProjection (F i))) (nonemptyFiniteDiagonal B n)) :=
  finiteCommonFiberProductBase_leftFibration n _ (fun _ ↦ inferInstance)

local instance (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : B _⦋0⦌) : KanComplex (nonemptyFiniteSSetProduct n
      (fun i ↦ vertexFiber (smallLeftUnstraighteningProjection (F i)) b)) :=
  nonemptyFiniteSSetProduct_kanComplex n _ (fun _ ↦ inferInstance)

/-- 元の指定比較の fiber 射は、積表示の下で元の全射影の fiber 射の対そのもの。 -/
lemma finiteCoherentSpaceProductTotalComparison_fiber (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : B _⦋0⦌) :
    vertexFiberMap (smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F))
      (pullback.snd (nonemptyFiniteSSetProductMap n
        (fun i ↦ smallLeftUnstraighteningProjection (F i))) (nonemptyFiniteDiagonal B n))
      (finiteCoherentSpaceProductTotalComparison n F)
      (finiteCoherentSpaceProductTotalComparison_base n F) b ≫
        (finiteCommonFiberProductVertexIso n
          (fun i ↦ smallLeftUnstraighteningProjection (F i)) b).hom =
            finiteCoherentProductSmallFiberMap n F b := by
  apply nonemptyFiniteSSetProduct_hom_ext n _
  intro i
  rw [Category.assoc, finiteCommonFiberProductVertexIso_projection,
    finiteCoherentProductSmallFiberMap_projection]
  apply vertexFiber_hom_ext _ b
  rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, vertexFiberMap_ι,
    vertexFiberMap_ι, Category.assoc, finiteCoherentSpaceProductTotalComparison_projection]

/-- 元の有限全空間比較の各頂点 fiber は同値。 -/
lemma finiteCoherentSpaceProductTotalComparison_fiber_isQCatEquivalence (n : ℕ)
    {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : B _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap
      (smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F))
      (pullback.snd (nonemptyFiniteSSetProductMap n
        (fun i ↦ smallLeftUnstraighteningProjection (F i))) (nonemptyFiniteDiagonal B n))
      (finiteCoherentSpaceProductTotalComparison n F)
      (finiteCoherentSpaceProductTotalComparison_base n F) b) := by
  apply (qCatEquivalenceOfIso (finiteCommonFiberProductVertexIso n
    (fun i ↦ smallLeftUnstraighteningProjection (F i)) b)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (_ ≫ (finiteCommonFiberProductVertexIso n
    (fun i ↦ smallLeftUnstraighteningProjection (F i)) b).hom)
  rw [finiteCoherentSpaceProductTotalComparison_fiber]
  exact finiteCoherentProductSmallFiberMap_isQCatEquivalence n F b

/-- 任意の小さい底上で、元の有限 coherent 積の指定全空間比較は前合成同値。 -/
lemma finiteCoherentSpaceProductTotalComparison_isPrecompositionEquivalence (n : ℕ)
    {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    IsPrecompositionEquivalence (finiteCoherentSpaceProductTotalComparison n F) :=
  isPrecompositionEquivalence_of_leftFibration_fibers _ _ _
    (finiteCoherentSpaceProductTotalComparison_base n F)
    (finiteCoherentSpaceProductTotalComparison_fiber_isQCatEquivalence n F)

/-- 同じ元の有限 coherent 積の指定全空間比較は弱ホモトピー同値。 -/
lemma finiteCoherentSpaceProductTotalComparison_isWeakHomotopyEquivalence (n : ℕ)
    {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    IsWeakHomotopyEquivalence (finiteCoherentSpaceProductTotalComparison n F) :=
  (finiteCoherentSpaceProductTotalComparison_isPrecompositionEquivalence n F
    ).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
