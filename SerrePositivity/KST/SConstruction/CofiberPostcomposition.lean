module
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection
public import SerrePositivity.KST.SConstruction.CofiberEvaluations

/-! # 完全関手による全 cofiber 図式の後合成
概要：零対象と cofiber を保つ射は全 cofiber 図式を保つ。
方針：元の正方形を後合成し、零角と押し出しの条件で全部分複体へ持ち上げる。
規約：選んだ cofiber 関手への置換はしない。使われ方：加法性の入力に関する自然性。
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

/-- 内部 Hom の後合成は零対象と cofiber の保存を保つ。 -/
lemma ihom_map_preservesCofiberData {A C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) : PreservesCofiberData ((ihom A).map f) := by
  constructor
  · intro z hz
    exact functor_postcomp_isZeroVertex f hf.1 hz
  · intro t ht
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
    intro a
    rw [Category.assoc, ihom_postcomp_evaluate, ← Category.assoc]
    let T : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle C := ⟨t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a,
      isZeroVertex_evaluateFunctorAt t.zero_corner a⟩
    exact hf.2 T ((functor_zeroTriangle_pushout_iff t).1 ht a)

/-- 元の四角形の後合成は cofiber 頂点条件を保つ。 -/
lemma cofiberPostcomp_vertex {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesCofiberData f)
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌)
    (hv : IsCofiberDiagramVertex v) :
    IsCofiberDiagramVertex (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map f).app
      (Opposite.op ⦋0⦌) v) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map f).app
      (Opposite.op ⦋0⦌) v) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v ≫ f := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) D).injective
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) D)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) D).symm _) = _
    rw [Equiv.apply_symm_apply]
    change _ = ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map f).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v))
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) = v from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram _) 0 1) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram _)
  rw [he]
  exact ⟨hf.1 _ hv.1, hf.2 ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v, hv.1⟩ hv.2⟩

/-- 全 cofiber 図式の完全関手による後合成。 -/
def cofiberPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesCofiberData f) :
    cofiberDiagrams C ⟶ cofiberDiagrams D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map f) (fun v =>
      cofiberPostcomp_vertex f hf v.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v))

/-- cofiber 値への持ち上げは元の四角形の後合成を厳密に保持する。 -/
lemma cofiberPostcomp_ι {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesCofiberData f) :
    cofiberPostcomp f hf ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
        (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 後合成は四角形の各角の評価と厳密に可換。 -/
lemma cofiberPostcomp_evaluation {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesCofiberData f)
    (q : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    cofiberPostcomp f hf ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt q ≫ f := by
  rw [← Category.assoc, cofiberPostcomp_ι, Category.assoc, ihom_postcomp_evaluate]

end SerrePositivity.KST.SConstruction
