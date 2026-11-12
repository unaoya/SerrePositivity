module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeTailRestriction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeHeadSimplex

/-!
概要：tail と head の制限則から、始点固定 cone 全体の制限則を得る。
方針：tail の等式で表示を揃え、Hom の四分岐を照合する。
規約：退化拡張全体の自然性は使わない。
使われ方：weighted cone の実際の単体的自然性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- tail と head の同じ制限則は、始点固定 cone 全体の厳密な制限則を与える。 -/
lemma coherentConeSimplexOfHead_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (x : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (A : (SimplicialNerve C) _⦋n⦌) (B : (SimplicialNerve C) _⦋m⦌)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentConeHead x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension A))
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentConeHead x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension B))
    (h : (SimplicialNerve C).map α.op A = B)
    (hh : ∀ j : Fin (m + 1),
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫ H.hom (α.toOrderHom j) ≫
        eqToHom (congrArg (SimplicialCategory.sHom x)
          (congrArg (fun T : (SimplicialNerve C) _⦋m⦌ => T.obj ⟨ULift.up j⟩) h)) = K.hom j) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeSimplexOfHead x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension A) H) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeSimplexOfHead x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension B) K := by
  subst B
  refine EnrichedFunctor.ext SSet (fun i => ?_) (fun i j => ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    all_goals simp only [eqToHom_refl, Category.comp_id]
    case zero.zero =>
      change (_ ≫ SemiCartesianMonoidalCategory.toUnit _) ≫ eId SSet x =
        SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x
      rw [SemiCartesianMonoidalCategory.comp_toUnit]
    case zero.succ j =>
      change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
        H.hom (α.toOrderHom j) = K.hom j
      simpa only [eqToHom_refl, Category.comp_id] using hh j
    case succ.zero i =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ i j =>
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension_map_reindex α A i j

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
