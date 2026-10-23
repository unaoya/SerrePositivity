module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldHorizontalDetection
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：universal scaffold の相対制限は cocartesian 関手の全部分複体を厳密に反映する。
方針：水平辺による保存の判定を頂点条件へ移し、各次数で pullback の普遍性を確認する。
規約：元の相対関手の包含と元の前合成による四角形を使う。
使われ方：scaffold 制限の同値性を全相対 Hom の制限から回収するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の相対関手は、universal scaffold で制限した関手が全水平辺を保つことと同値。 -/
lemma cocartesianRelativeFunctorPredicate_iff_scaffold
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) [CocartesianFibration p] [InnerFibration q]
    (v : (relativeFunctorSpace q p) _⦋0⦌) :
    CocartesianScaffoldFunctorPredicate (kanCocartesianStrictTransportDiagram p) q
      ((relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))
        (V := Over.mk p) (kanUniversalScaffold p) (kanUniversalScaffold_projection p))).app _ v) ↔
      cocartesianRelativeFunctorPredicate p q v := by
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex q p v
  have hpre : (relativeFunctorOverPre q (Over.homMk
      (U := Over.mk (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))
      (V := Over.mk p) (kanUniversalScaffold p) (kanUniversalScaffold_projection p))).app
      (Opposite.op ⦋0⦌) (relativeFunctorVertex q p g hg) =
    relativeFunctorVertex q
      (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))
      (kanUniversalScaffold p ≫ g) (by
        rw [Category.assoc, hg, kanUniversalScaffold_projection]) := by
    apply Subtype.ext
    rfl
  rw [hpre, cocartesianScaffoldFunctorPredicate_vertex, cocartesianRelativeFunctorPredicate_vertex]
  constructor
  · exact preservesCocartesianEdges_of_kanUniversalScaffold_horizontal p q g
  · intro hc c d f x
    exact hc _ (kanUniversalScaffold_horizontal p f x)

/-- 水平辺を保つ相対制限の四角形は、元の全相対 Hom と二つの包含の厳密な pullback。 -/
lemma cocartesianStrictTransportScaffoldRestriction_isPullback
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) [CocartesianFibration p] [InnerFibration q] :
    IsPullback (cocartesianStrictTransportScaffoldRestriction p q)
      (cocartesianRelativeFunctorInclusion p q)
      (cocartesianScaffoldFunctorInclusion (kanCocartesianStrictTransportDiagram p) q)
      (relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))
        (V := Over.mk p) (kanUniversalScaffold p) (kanUniversalScaffold_projection p))) := by
  let R := relativeFunctorOverPre q (Over.homMk
    (U := Over.mk (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))
    (V := Over.mk p) (kanUniversalScaffold p) (kanUniversalScaffold_projection p))
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    exact h.2
  · rintro ⟨v, hv⟩ w he
    change v = R.app d w at he
    have hw : ∀ α : ⦋0⦌ ⟶ d.unop,
        cocartesianRelativeFunctorPredicate p q ((relativeFunctorSpace q p).map α.op w) := by
      intro α
      apply (cocartesianRelativeFunctorPredicate_iff_scaffold p q _).mp
      have hc : CocartesianScaffoldFunctorPredicate (kanCocartesianStrictTransportDiagram p) q
          ((relativeFunctorSpace q
            (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map
              α.op v) := hv α
      have hn := ConcreteCategory.congr_hom (R.naturality α.op) w
      change R.app (Opposite.op ⦋0⦌) ((relativeFunctorSpace q p).map α.op w) =
        (relativeFunctorSpace q
          (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map
            α.op (R.app d w) at hn
      have hvr : (relativeFunctorSpace q
          (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map α.op v =
          R.app (Opposite.op ⦋0⦌) ((relativeFunctorSpace q p).map α.op w) :=
        (congrArg (fun t => (relativeFunctorSpace q
          (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map α.op t)
            he).trans hn.symm
      intro c d f x
      exact (Eq.mp (congrArg
        (CocartesianScaffoldFunctorPredicate (kanCocartesianStrictTransportDiagram p) q) hvr)
          @hc) f x
    exact ⟨⟨w, hw⟩, Subtype.ext he.symm, rfl⟩

end SerrePositivity.InfinityCategories
