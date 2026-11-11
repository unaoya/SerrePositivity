module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexNerveColimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
概要：余極限上の単体圏の関手の反転条件を、図式の各対象で検出する。
方針：nerve の余極限保存と一次単体の共同全射性を使う。
規約：底の図式に単射性も連結性も要求しない。
使われ方：反転関手の小余積・transfinite な図式の極限表示。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 余極限上で指定辺を反転する条件は、図式の各対象への全ての制限で検出できる。 -/
lemma transportSimplexInvertsEdges_of_isColimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) {E : SSet.{max u v}}
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory c.pt) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges c.pt) ↔
      ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j)) ≫ U)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (F.obj j)) := by
  constructor
  · intro h j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertsEdges_restrict (c.ι.app j) U h
  · intro h s hs
    let e := (evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj (Opposite.op ⦋1⦌)
    have ht := isColimitOfPreserves e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveCoconeIsColimit hc)
    obtain ⟨j, t, he⟩ := Types.jointly_surjective _ ht s
    change (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j))).app (Opposite.op ⦋1⦌) t = s at he
    subst s
    have htW := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges_map_iff (c.ι.app j) t).mp hs
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex t).map
      ((truncation 2).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j)) ≫ U)))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j))).app (Opposite.op ⦋1⦌) t)).map
          ((truncation 2).map U)) rfl).mp (h j htW)

/-- 反転関手の図式の包含は、単体圏上の全関手の図式への自然変換。 -/
def transportSimplexInvertingInclusion (E : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingDiagram E ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveFunctor.op ⋙ internalHom.flip.obj E where
  app B := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.unop)) E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B.unop)).ι
  naturality {_B _D} f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction_ι f.unop E

/-- 反転関手の全部分複体の頂点条件も、余極限の各対象で検出できる。 -/
lemma isInvertingFunctorVertex_iff_of_isColimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) {E : SSet.{max u v}}
    (v : ((ihom (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory c.pt))).obj E) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges c.pt) v ↔
      ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (F.obj j))
        (((pre (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j)))).app E).app
          (Opposite.op ⦋0⦌) v) := by
  obtain ⟨U, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ E).surjective v
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex
  rw [Equiv.symm_apply_apply]
  refine (transportSimplexInvertsEdges_of_isColimit hc U).trans ?_
  apply forall_congr'
  intro j
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j)) ≫ U) _ ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ E).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ E)
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (c.ι.app j)) ≫ U))) _
  rw [Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
