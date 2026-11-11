module
public import SerrePositivity.KST.SConstruction.FullSubcomplexLimits
public import SerrePositivity.KST.SConstruction.CofiberEndofunctor

/-! # 安定な全部分圏の頂点の閉性条件
概要：零対象・押し出し・引き戻しと同型に閉じた頂点条件をまとめる。
方針：周囲の実際の普遍四角形の四つの角で閉性を述べる。
規約：部分圏の安定性や包含の完全性を仮定には置かない。使われ方：相対 cofiber 図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 零対象と全押し出し・引き戻しに閉じた replete な頂点条件。 -/
structure ClosedStablePredicate (X : StableModel.{u}) where
  predicate : X.carrier _⦋0⦌ → Prop
  of_iso {x y : X.carrier _⦋0⦌} : predicate x → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → predicate y
  zero_mem {z : X.carrier _⦋0⦌} : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z → predicate z
  pushout_mem (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F → predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) →
      predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) → predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) →
        predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1)
  pullback_mem (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F → predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) →
      predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) → predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1) →
        predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)

/-- 閉じた頂点条件が定める全高次単体を持つ全部分圏。 -/
def closedSubcategory {X : StableModel.{u}} (P : ClosedStablePredicate X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate

/-- 閉じた全部分圏は quasicategory。 -/
instance closedSubcategory_quasicategory {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    Quasicategory (closedSubcategory P) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate : SSet.{u}))

/-- 閉じた全部分圏の頂点は定義の条件を満たす。 -/
lemma closedSubcategory_vertex {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (v : (closedSubcategory P) _⦋0⦌) : P.predicate v.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v

/-- 四角形の四つの角の条件から全頂点での条件を得る。 -/
lemma square_vertices_of_corners {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (h00 : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) (h10 : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0))
    (h01 : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1)) (h11 : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1)) :
    ∀ q, P (F.app (Opposite.op ⦋0⦌) q) := by
  rintro ⟨a, b⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  fin_cases i <;> fin_cases j <;> assumption

/-- 頂点条件を持つ周囲の頂点を全部分圏の頂点として保持する。 -/
def fullSubcategoryVertex {X : SSet.{u}} (P : X _⦋0⦌ → Prop) (x : X _⦋0⦌) (hx : P x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌ :=
  ⟨x, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hx⟩

/-- 閉じた全部分圏は実際の零対象を持つ。 -/
instance closedSubcategory_hasZeroVertex {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (closedSubcategory P) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X.carrier
  let v := fullSubcategoryVertex P.predicate z.vertex (P.zero_mem z.isZero)
  exact ⟨⟨v, isInitialVertex_fullSubcomplex_of_ambient P.predicate v z.isInitial,
    isTerminalVertex_fullSubcomplex_of_ambient P.predicate v z.isTerminal⟩⟩

end SerrePositivity.KST.SConstruction
