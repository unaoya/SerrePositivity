module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：通常の自然変換から作った coherent な辺を、全ての対角単体で計算する。
方針：区間の通常の図式を uncurry した射列と、元の混合 Hom の評価を比較する。
規約：頂点での評価だけでなく、底の射列と区間の全単体を同時に動かす。
使われ方：G8 の四角形①で、元の spaceDiagramEdge の区間模型を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local implicit_reducible] Monotone
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

attribute [local implicit_reducible] KanDiagramObject

variable {C : Type u} [Category.{u} C] {F G : KanDiagramObject C}

/-- 忘却後の通常の自然変換を、元の Kan 複体の図式の自然変換として読む。 -/
def kanDiagramUnderlyingTransformation
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) : F.val ⟶ G.val where
  app c := η.app c
  naturality {_ _} f := η.naturality f

/-- 区間の射と底の射列を同時に評価する元の通常の図式。 -/
def kanDiagramEdgeOrderDiagram
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    {n : ℕ} (σ : (nerve C) _⦋n⦌) (α : ⦋n⦌ ⟶ ⦋1⦌) :
    ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u} :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
    (α.toOrderHom.toFunctor.prod' σ) ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation η))

/-- 区間の二頂点間の混合評価は、同じ通常の自然変換と底の射の合成である。 -/
lemma kanDiagramEdge_mixed_constant
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (a b : Fin 2) (hab : a ≤ b) {c d : C} (f : c ⟶ d) (k : SimplexCategoryᵒᵖ) :
    HEq
      ((strictDiagramMixedHom f
        (((ComposableArrows.mk₁ (kanDiagramHom η)).obj a).val ⋙ kanObjectForget)
        (((ComposableArrows.mk₁ (kanDiagramHom η)).obj b).val ⋙ kanObjectForget)).app k
          (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
            (SimplicialCategory.homEquiv' _ _
              ((ComposableArrows.mk₁ (kanDiagramHom η)).map (homOfLE hab))) k.unop.len))
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (SimplicialCategory.homEquiv' _ _
          (((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation η)).map (homOfLE hab)).app c ≫
            ((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation η)).obj b).map f))
        k.unop.len) := by
  fin_cases a <;> fin_cases b
  all_goals first
  | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hab)
  | apply heq_of_eq
    apply CategoryTheory.Functor.functorHom_ext
    intro m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 元の実現した辺の任意の対角単体は、同じ通常の区間図式の coherent 表示である。 -/
lemma kanDiagramDiagonalSimplex_edge
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    {n : ℕ} (σ : (nerve C) _⦋n⦌) (α : ⦋n⦌ ⟶ ⦋1⦌) :
    kanDiagramDiagonalSimplex σ
      ((KanDiagramNerve C).map α.op (coherentNerveEdge (kanDiagramHom η)).edge) =
    enrichedFunctorOfOrderDiagram (kanDiagramEdgeOrderDiagram η σ α) := by
  change Fin (n + 1) ⥤ C at σ
  rcases F with ⟨F, hF⟩
  rcases G with ⟨G, hG⟩
  change kanDiagramDiagonalSimplex σ
    ((SimplicialNerve (KanDiagramObject C)).map α.op
      (coherentNerveEdge (kanDiagramHom η)).edge) = _
  rw [coherentNerveEdge_edge, ← NatTrans.naturality_apply]
  change diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ)
    (enrichedFunctorOfOrderDiagram
      ((⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
        α.toOrderHom.toFunctor ⋙ ComposableArrows.mk₁ (kanDiagramHom η))) = _
  have ho : ∀ i, (kanDiagramDiagonalSimplex σ
      ((KanDiagramNerve C).map α.op (coherentNerveEdge (kanDiagramHom η)).edge)).obj i =
      (enrichedFunctorOfOrderDiagram (kanDiagramEdgeOrderDiagram η σ α)).obj i := by
    intro i
    change ((ComposableArrows.mk₁ (kanDiagramHom η)).obj (α.toOrderHom i.as.down)).val.obj
      (σ.obj i.as.down) =
      ((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation η)).obj
        (α.toOrderHom i.as.down)).obj (σ.obj i.as.down)
    generalize α.toOrderHom i.as.down = a
    fin_cases a <;> rfl
  refine EnrichedFunctor.ext SSet ho ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change ((diagonalKanDiagramHom (kanDiagramSimplexBase σ) _ i j ≫ eqToHom _).app d) P = _
  have hcast {A B D : SSet.{u}} (f : A ⟶ B) (h : B = D)
      (k : SimplexCategoryᵒᵖ) (x : A.obj k) :
      HEq ((f ≫ eqToHom h).app k x) (f.app k x) := by
    subst D
    rfl
  apply eq_of_heq
  refine (hcast _ _ d P).trans ?_
  change HEq ((diagonalKanDiagramHom (kanDiagramSimplexBase σ) _ i j).app d P) _
  erw [diagonalKanDiagramHom_of_le _ _ i j hij]
  exact kanDiagramEdge_mixed_constant η (α.toOrderHom i.as.down)
    (α.toOrderHom j.as.down) (α.toOrderHom.monotone hij)
    (σ.map (homOfLE hij)) d


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
