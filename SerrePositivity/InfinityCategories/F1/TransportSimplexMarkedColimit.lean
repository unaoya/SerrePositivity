module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexNerveColimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
概要：余極限上の単体圏の関手の反転条件を、図式の各対象で検出する。
方針：nerve の余極限保存と一次単体の共同全射性を使う。
規約：底の図式に単射性も連結性も要求しない。
使われ方：反転関手の小余積・transfinite な図式の極限表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 余極限上で指定辺を反転する条件は、図式の各対象への全ての制限で検出できる。 -/
lemma transportSimplexInvertsEdges_of_isColimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) {E : SSet.{max u v}}
    (U : nerve (TransportSimplexCategory c.pt) ⟶ E) :
    InvertsEdges U (transportSimplexInitialEdges c.pt) ↔
      ∀ j, InvertsEdges (nerveMap (transportSimplexFunctor (c.ι.app j)) ≫ U)
        (transportSimplexInitialEdges (F.obj j)) := by
  constructor
  · intro h j
    exact transportSimplexInvertsEdges_restrict (c.ι.app j) U h
  · intro h s hs
    let e := (evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj (Opposite.op ⦋1⦌)
    have ht := isColimitOfPreserves e (transportSimplexNerveCoconeIsColimit hc)
    obtain ⟨j, t, he⟩ := Types.jointly_surjective _ ht s
    change (nerveMap (transportSimplexFunctor (c.ι.app j))).app (Opposite.op ⦋1⦌) t = s at he
    subst s
    have htW := (transportSimplexInitialEdges_map_iff (c.ι.app j) t).mp hs
    exact (isInvertibleEdge_congr (e := (edgeOfSimplex t).map
      ((truncation 2).map (nerveMap (transportSimplexFunctor (c.ι.app j)) ≫ U)))
      (f := (edgeOfSimplex
        ((nerveMap (transportSimplexFunctor (c.ι.app j))).app (Opposite.op ⦋1⦌) t)).map
          ((truncation 2).map U)) rfl).mp (h j htW)

/-- 反転関手の図式の包含は、単体圏上の全関手の図式への自然変換。 -/
def transportSimplexInvertingInclusion (E : SSet.{u}) :
    transportSimplexInvertingDiagram E ⟶
      transportSimplexNerveFunctor.op ⋙ internalHom.flip.obj E where
  app B := (invertingFunctors (nerve (TransportSimplexCategory B.unop)) E
    (transportSimplexInitialEdges B.unop)).ι
  naturality {_B _D} f := transportSimplexInvertingRestriction_ι f.unop E

/-- 反転関手の全部分複体の頂点条件も、余極限の各対象で検出できる。 -/
lemma isInvertingFunctorVertex_iff_of_isColimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) {E : SSet.{max u v}}
    (v : ((ihom (nerve (TransportSimplexCategory c.pt))).obj E) _⦋0⦌) :
    IsInvertingFunctorVertex _ E (transportSimplexInitialEdges c.pt) v ↔
      ∀ j, IsInvertingFunctorVertex _ E (transportSimplexInitialEdges (F.obj j))
        (((pre (nerveMap (transportSimplexFunctor (c.ι.app j)))).app E).app
          (Opposite.op ⦋0⦌) v) := by
  obtain ⟨U, rfl⟩ := (functorVertexEquiv _ E).surjective v
  unfold IsInvertingFunctorVertex
  rw [Equiv.symm_apply_apply]
  refine (transportSimplexInvertsEdges_of_isColimit hc U).trans ?_
  apply forall_congr'
  intro j
  change InvertsEdges (nerveMap (transportSimplexFunctor (c.ι.app j)) ≫ U) _ ↔
    InvertsEdges ((functorVertexEquiv _ E).symm ((functorVertexEquiv _ E)
      (nerveMap (transportSimplexFunctor (c.ι.app j)) ≫ U))) _
  rw [Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories
