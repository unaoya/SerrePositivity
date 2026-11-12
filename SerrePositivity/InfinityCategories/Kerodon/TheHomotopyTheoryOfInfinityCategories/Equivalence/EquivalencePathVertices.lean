module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration

/-!
概要：可逆な辺を path の頂点として表示し、置換の頂点上の全射性を示す。
方針：ホモトピー圏の同型を実際の辺で表し、引き戻しへ含める。
規約：本質的全射性は元の関手に仮定する。
使われ方：Kerodon §4.8.1（Tag 01JG）、Theorem 4.8.4.1（Tag 01JX） の射の置換。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：可逆な辺が表す可逆 path の頂点。
方針：辺の Yoneda 表示を関手の頂点とし、全部分複体に含める。
規約：標的に quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.8.1（Tag 01JG） の頂点の表示。 -/
def equivalencePathVertex {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, CategoryTheory.Functor.map_id_apply]
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge) (f := e) rfl).mpr he⟩

/-- 概要：辺からの path の始点は元の辺の始点。
方針：区間の零頂点で Yoneda 表示を評価する。
規約：与えた辺の端点を使う。
使われ方：Kerodon §4.5.3（Tag 032Y） の始点の識別。 -/
lemma equivalencePathVertex_zero {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = x := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge)) = x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  rw [h]
  exact e.src_eq

/-- 概要：辺からの path の終点は元の辺の終点。
方針：区間の一頂点で Yoneda 表示を評価する。
規約：与えた辺の端点を使う。
使われ方：Kerodon §4.5.3（Tag 032Y） の終点の識別。 -/
lemma equivalencePathVertex_one {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = y := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge)) = y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by decide
  rw [h]
  exact e.tgt_eq

/-- 概要：本質的全射な関手の path による置換は頂点上で全射。
方針：各標的頂点へのホモトピー圏の同型を可逆な辺で表し、引き戻しへ送る。
規約：標的 Y が quasicategory、始域の quasicategory 性は不要。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の全射な射への還元。 -/
lemma IsEssentiallySurjective.equivalencePathReplacementMap_surjective {X Y : SSet.{u}}
    [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := hf y
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (f.app (Opposite.op ⦋0⦌) x) y e.hom
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge s := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk s)
    rw [hs]
    infer_instance
  let v := equivalencePathVertex s he
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0).app (Opposite.op ⦋0⦌) v =
      f.app (Opposite.op ⦋0⦌) x := equivalencePathVertex_zero s he
  let a := SSet.yonedaEquiv.symm v
  let b := SSet.yonedaEquiv.symm x
  have hw : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = b ≫ f := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hv]
  let l := pullback.lift a b hw
  refine ⟨SSet.yonedaEquiv l, ?_⟩
  have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 := by
    change l ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = _
    rw [← Category.assoc, pullback.lift_fst]
  have h := congrArg SSet.yonedaEquiv hl
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h.trans (equivalencePathVertex_one s he)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEssentiallySurjective (equivalencePathReplacementMap_surjective)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
