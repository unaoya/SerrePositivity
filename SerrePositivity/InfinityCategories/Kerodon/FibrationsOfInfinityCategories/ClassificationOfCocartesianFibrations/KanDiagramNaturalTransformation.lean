module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramConstantParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMappingVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber

/-!
概要：通常の Kan 値図式の自然変換を coherent な図式間の辺へ写す。
方針：変換空間の零単体を実現し、各対象での評価を計算する。
規約：全 strict 変換空間の Kan 性は仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、反転した係数の共通解像の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な Kan 値図式の実現は頂点で元の coherent な図式を回収する。
方針：関手空間の各単体で、図式パラメーターが定値な対角評価を計算する。
規約：始域の図式は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、自然変換の実現の端点。 -/
lemma kanDiagramRealization_vertex {C : Type u} [Category.{u} C] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F.val) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex σ
    ((SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)).map α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex F)) = _
  have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex_constant F σ

/-- 概要：通常の自然変換を Kan 値図式の豊穣圏の通常の射として表す。
方針：変換の頂点をテンソル単位からの射へ移す。
規約：η は単体集合へ忘却した図式の自然変換。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な辺を作る入力。 -/
def kanDiagramHom {C : Type u} [Category.{u} C] {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) : F ⟶ G :=
  (SSet.unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex η)

/-- 概要：自然変換の実現は二つの coherent な図式の間の辺。
方針：豊穣圏の通常の辺を実現し、頂点の公式で端点を同定する。
規約：端点は kanDiagramCoherentNerve に揃える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の図式の比較を関手 ∞ 圏で扱う。 -/
noncomputable def kanDiagramNaturalTransformationEdge {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve G.val)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kanDiagramHom η)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C)).ofEq
    (kanDiagramRealization_vertex F) (kanDiagramRealization_vertex G)

/-- 概要：自然変換を実現した辺の対象 c での評価は成分の coherent な辺。
方針：実現と評価の可換式を使い、二頂点の豊穣関手の Hom を計算する。
規約：一単体の厳密な等式として比較する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、成分の同値性を実現した辺の可逆性へ移す。 -/
lemma kanDiagramNaturalTransformationEdge_at {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (kanDiagramNaturalTransformationEdge η) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show F.val.obj c ⟶ G.val.obj c from η.app c)).edge := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kanDiagramHom η)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C) |>.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))).edge = _
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app
    (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kanDiagramHom η)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_evaluate]
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    fin_cases i <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    fin_cases i <;> fin_cases j
    all_goals
      simp only [eqToHom_refl, Category.comp_id]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      first
      | rfl
      | have h := SimplicialThickening.Path.le (P.obj 0)
        exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)

/-- 概要：対象ごとに同値な通常の自然変換の実現は可逆な辺。
方針：底の任意の頂点を対象で表示し、成分の辺の可逆性を点ごとの判定に使う。
規約：strict 変換空間の Kan 性を使わず、関手空間で判定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、自然な共通解像からの coherent な同型。 -/
lemma kanDiagramNaturalTransformationEdge_isInvertible {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (kanDiagramNaturalTransformationEdge η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt
    (kanDiagramNaturalTransformationEdge η).toTruncated).mpr
  rintro ⟨s⟩
  obtain ⟨c, rfl⟩ : ∃ c : C, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (kanDiagramNaturalTransformationEdge η) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _))).toTruncated
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (kanDiagramNaturalTransformationEdge_at η _)).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence (hη _)

/-- 概要：対象ごとの同値である自然変換は coherent な Kan 値図式の関手同型を与える。
方針：構成済みの可逆な辺のホモトピー圏の射を同型に束縛する。
規約：順方向の射は実現した自然変換の辺の類。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な自然な比較を図式全体の同型へ移す。 -/
noncomputable def kanDiagramFunctorIsoOfPointwise {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve G.val) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (kanDiagramNaturalTransformationEdge η).toTruncated) :=
    kanDiagramNaturalTransformationEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (kanDiagramNaturalTransformationEdge η).toTruncated)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
