module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallPointWitnessContractible
public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplexFibers

/-!
概要：大きい Kan 複体が小さい Kan 模型を持つという、同値不変な小ささの条件。
方針：小さい Kan 複体の宇宙持ち上げとの実際の圏同値を使う。
規約：元の単体の集合が各次数で小さいことは要求しない。
使われ方：essentially small な fiber の相対表現への延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 大きい Kan 複体が、元の宇宙の Kan 複体と同値であるという条件。 -/
def HasSmallKanModel (X : SSet.{u + 1}) [Quasicategory X] : Prop :=
  ∃ K : KanObject.{u}, Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K.obj) X)

/-- 小さい Kan 模型を持つという条件は、同じ大きい宇宙の圏同値で保たれる。 -/
lemma HasSmallKanModel.of_equivalence {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (h : HasSmallKanModel X) (e : QCatEquivalence X Y) :
    HasSmallKanModel Y := by
  obtain ⟨K, ⟨d⟩⟩ := h
  exact ⟨K, ⟨d.trans e⟩⟩

/-- 実際に各次数で小さい Kan 複体は、次数ごとの縮小から小さい Kan 模型を持つ。 -/
lemma hasSmallKanModel_of_small (X : SSet.{u + 1}) [KanComplex X]
    [∀ n, Small.{u} (X.obj n)] : HasSmallKanModel X := by
  let K := smallSimplicialSet.{u, u + 1} X
  let e := smallSimplicialSetIso.{u, u + 1} X
  have : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj K) :=
    HomotopyLimits.kanComplex_of_iso e.symm
  have : KanComplex K := DoldKanComparison.kanComplex_of_ulift.{u + 1, u} K
  exact ⟨⟨K, inferInstance⟩, ⟨qCatEquivalenceOfIso e⟩⟩

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 各頂点上の実際の Kan fiber が小さい Kan 模型を持つという条件。 -/
def HasEssentiallySmallFibers {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] : Prop :=
  ∀ b, HasSmallKanModel (vertexFiber p b)

/-- 既存の次数 fiber の小ささは、同値不変な fiber の小ささを含意する。 -/
lemma HasSmallSimplexFibers.essentiallySmall {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (hp : HasSmallSimplexFibers p) :
    HasEssentiallySmallFibers p := by
  intro b
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((vertexFiber p b).obj n) :=
    hp n (PinchedHom.constant b n.unop.len)
  exact hasSmallKanModel_of_small _

end SerrePositivity.InfinityCategories
