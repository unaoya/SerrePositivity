module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：選んだ関手族の上で可逆となるホモトピーの前合成作用。
方針：前合成の二胞体を族へ制限し、各関手での評価を後合成されたホモトピーと照合する。
規約：元のホモトピーの全成分の可逆性は要求しない。
使われ方：B2 の W を反転する関手族の上で反射単位を自然同型にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：各関手がホモトピーの成分を可逆にする族の上では前合成作用は自然同型。
方針：前合成の辺を族へ制限し、二段階の点ごとの可逆性判定を使う。
規約：K の quasicategory 性と元のホモトピーの可逆性は不要。
使われ方：反射的局所化の反転関手圏上の単位の同型。 -/
def functorIsoRestrictedPrecompositionOfHomotopy {A B K Z : SSet.{u}} [Quasicategory Z]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (q : K ⟶ (ihom B).obj Z)
    (hH : ∀ (v : K _⦋0⦌) (u : B ⟶ Z), q.app (Opposite.op ⦋0⦌) v = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u →
      ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated.map ((truncation 2).map u))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ (pre f).app Z) (q ≫ (pre g).app Z) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  let m : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre f).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre g).app Z)) :=
    { edge := s.app (Opposite.op ⦋1⦌) e.edge
      src_eq := (e.map ((truncation 2).map s)).src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex f)
      tgt_eq := (e.map ((truncation 2).map s)).tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex g) }
  let t : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj ((ihom A).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ (pre f).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ (pre g).app Z)) :=
    { edge := ((pre q).app ((ihom A).obj Z)).app (Opposite.op ⦋1⦌) m.edge
      src_eq := (m.map ((truncation 2).map ((pre q).app ((ihom A).obj Z)))).src_eq
      tgt_eq := (m.map ((truncation 2).map ((pre q).app ((ihom A).obj Z)))).tgt_eq }
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge t := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt t).mpr
    intro v
    obtain ⟨u, hu⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B Z).surjective (q.app (Opposite.op ⦋0⦌) v)
    let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H u
    have hH' : ∀ a : A _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' a).toTruncated := by
      intro a
      exact hH v u hu.symm a
    have hinv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H' hH'
    have he : (t.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) v))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H').edge := by
      have hp := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp (X := (ihom A).obj Z) q v)
          (Opposite.op ⦋1⦌)) m.edge
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) v).app (Opposite.op ⦋1⦌)
        (((pre q).app ((ihom A).obj Z)).app (Opposite.op ⦋1⦌) m.edge) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z)
            (q.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋1⦌) m.edge at hp
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) v).app (Opposite.op ⦋1⦌)
        (((pre q).app ((ihom A).obj Z)).app (Opposite.op ⦋1⦌) m.edge) = _
      rw [hp, ← hu]
      have hs := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorPrecompositionMap_evaluate (A := A) u)
          (Opposite.op ⦋1⦌)) e.edge
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u)).app (Opposite.op ⦋1⦌)
        (s.app (Opposite.op ⦋1⦌) e.edge) =
          ((ihom A).map u).app (Opposite.op ⦋1⦌) e.edge at hs
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u)).app (Opposite.op ⦋1⦌)
        (s.app (Opposite.op ⦋1⦌) e.edge) = _
      rw [hs]
      change ((ihom A).map u).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
        SSet.yonedaEquiv (curry (H.h ≫ u))
      rw [← SSet.yonedaEquiv_comp, curry_natural_right]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hinv
  haveI := ht
  exact asIso (SSet.Truncated.HomotopyCategory.homMk t)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
