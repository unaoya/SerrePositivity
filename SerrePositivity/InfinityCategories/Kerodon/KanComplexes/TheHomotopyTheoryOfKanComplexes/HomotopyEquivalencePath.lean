module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeEquivalencePathExtension

/-!
概要：可逆な指定ホモトピーを同じ代表のまま可逆 path の族へ写す。
方針：円柱を時間が第一因子となるよう交換し、可逆辺の全部分複体へ持ち上げる。
規約：像が定値な場合は、その定値性を射の等式として保つ。
使われ方：相対左 Kan の指定単位から底で定値な厳密化用 path を作る。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：定値な円柱を持つ指定ホモトピーの辺は可逆。
方針：同じ raw な辺を関手頂点の恒等辺と比較する。
規約：端点の型表示が異なっても代表の等式だけで比較する。
使われ方：底で定値な指定単位の像の可逆性を回収する。 -/
lemma kanHomotopy_isInvertible_of_constant {K D : SSet.{u}} {f g : K ⟶ D}
    (H : SSet.Homotopy f g) (q : K ⟶ D)
    (h : H.h = fst K (Δ[1] : SSet.{u}) ≫ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)).edge := by
    change SSet.yonedaEquiv (curry H.h) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q) 1
    rw [h]
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：指定ホモトピーの可逆な辺を同じ円柱の可逆 path として表す。
方針：各点の評価で可逆性を読み、全部分複体への持ち上げを使う。
規約：h Fun の射の代表を選び直さない。
使われ方：底で定値な指定単位の厳密な持ち上げ。 -/
def kanHomotopyEquivalencePath {K D : SSet.{u}} [Quasicategory D]
    {f g : K ⟶ D} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)) (fun x ↦ by
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) hi x
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.simplicialHomotopyOfFunctorEdge_of_homotopy] at hx
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
        (show H.h.app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge from ?_)).2 hx
      change H.h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        H.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj K) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
      have he : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro j
        fin_cases j <;> rfl
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, he])

/-- 概要：指定可逆ホモトピーの path の包含は元の円柱の curry。
方針：全部分複体への持ち上げの包含公式。
規約：時間は第一因子。
使われ方：端点と標的の像を厳密に計算する。 -/
lemma kanHomotopyEquivalencePath_ι {K D : SSet.{u}} [Quasicategory D]
    {f g : K ⟶ D} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
    kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι D =
      curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：可逆 path として表した指定ホモトピーの始点は元の始点。
方針：curry の評価と braiding の端点公式を使う。
規約：元の射 f との厳密な等式。
使われ方：厳密化で固定する部分図式を識別する。 -/
lemma kanHomotopyEquivalencePath_zero {K D : SSet.{u}} [Quasicategory D]
    {f g : K ⟶ D} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
    kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 0 = f := by
  change kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι D ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = f
  rw [← Category.assoc,kanHomotopyEquivalencePath_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
  exact H.h₀

/-- 概要：可逆 path として表した指定ホモトピーの終点は元の終点。
方針：curry の評価と braiding の端点公式を使う。
規約：元の射 g との厳密な等式。
使われ方：延長後も固定する大域図式を識別する。 -/
lemma kanHomotopyEquivalencePath_one {K D : SSet.{u}} [Quasicategory D]
    {f g : K ⟶ D} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
    kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 1 = g := by
  change kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι D ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = g
  rw [← Category.assoc,kanHomotopyEquivalencePath_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
  exact H.h₁

/-- 概要：底で定値な指定ホモトピーは定値な可逆 path に写る。
方針：包含の単射性で内部 Hom へ戻し、curry の自然性で円柱の像を計算する。
規約：底での定値性は元の代表 H.h に課す。
使われ方：元と標的の図式を同時に保つ相対厳密化。 -/
lemma kanHomotopyEquivalencePath_map_of_constant {K D E : SSet.{u}} [Quasicategory D]
    {f g : K ⟶ D} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) (U : D ⟶ E) (q : K ⟶ E)
    (hU : H.h ≫ U = fst K (Δ[1] : SSet.{u}) ≫ q) :
    kanHomotopyEquivalencePath H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap U = q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl E := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, kanHomotopyEquivalencePath_ι,
    ← curry_natural_right, Category.assoc, hU, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
