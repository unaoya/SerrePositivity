module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldMapping
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverPrecomposition

/-!
概要：cocartesian 相対 Hom を水平辺を保つ scaffold の相対 Hom へ制限する。
方針：scaffold の水平辺の条件を使い、元の底上の前合成を全部分複体へ持ち上げる。
規約：同じ前合成と同じ strict transport の作用の可換三角形を厳密に示す。
使われ方：cocartesian strict transport の写像空間比較の同値性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 水平辺を cocartesian に送る底上の射に沿う、元の cocartesian 相対 Hom の制限。 -/
def cocartesianScaffoldPrecomposition {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E D : SSet.{u}} (p : E ⟶ nerve C) (q : D ⟶ nerve C)
    (l : simplicialReplacement F ⟶ E) (hl : l ≫ p = simplicialReplacementProjection F)
    (hc : ∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌),
      IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌) (kanScaffoldHorizontalEdge F f x))) :
    cocartesianRelativeFunctorSpace p q ⟶ CocartesianScaffoldFunctorSpace F q :=
  fullSubcomplexLift _ (cocartesianRelativeFunctorInclusion p q ≫
    relativeFunctorOverPre q (Over.homMk (U := Over.mk (simplicialReplacementProjection F))
      (V := Over.mk p) l hl)) (by
    intro v
    obtain ⟨g, hg, hv⟩ := exists_relativeFunctorVertex q p v.val
    have hco := fullSubcomplexOnVertices_vertex v
    change cocartesianRelativeFunctorPredicate p q v.val at hco
    rw [← hv, cocartesianRelativeFunctorPredicate_vertex] at hco
    change CocartesianScaffoldFunctorPredicate F q
      ((relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (simplicialReplacementProjection F)) (V := Over.mk p) l hl)).app _ v.val)
    rw [← hv]
    have hpre : (relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (simplicialReplacementProjection F)) (V := Over.mk p) l hl)).app
        (Opposite.op ⦋0⦌) (relativeFunctorVertex q p g hg) =
      relativeFunctorVertex q (simplicialReplacementProjection F) (l ≫ g)
        (by rw [Category.assoc, hg, hl]) := by
      apply Subtype.ext
      rfl
    rw [hpre, cocartesianScaffoldFunctorPredicate_vertex]
    intro c d f x
    exact hco _ (hc f x))

/-- universal scaffold の制限は、元の全 cocartesian 相対 Hom の一つの単体集合の射。 -/
def cocartesianStrictTransportScaffoldRestriction {C : Type u} [Category.{u} C]
    {E D : SSet.{u}} (p : E ⟶ nerve C) (q : D ⟶ nerve C) :
    cocartesianRelativeFunctorSpace p q ⟶
      CocartesianScaffoldFunctorSpace (kanCocartesianStrictTransportDiagram p) q :=
  cocartesianScaffoldPrecomposition (kanCocartesianStrictTransportDiagram p) p q
    (kanUniversalScaffold p) (kanUniversalScaffold_projection p) (kanUniversalScaffold_horizontal p)

/-- 同じ strict transport の全作用を scaffold で評価すると元の universal scaffold 制限となる。 -/
lemma cocartesianStrictTransportMappingSpaceMap_scaffold
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) :
    cocartesianStrictTransportMappingSpaceMap p q ≫
      cocartesianDiagramScaffoldMappingSpaceMap (kanCocartesianStrictTransportDiagram p) q =
        cocartesianStrictTransportScaffoldRestriction p q := by
  apply (cancel_mono
    (cocartesianScaffoldFunctorInclusion (kanCocartesianStrictTransportDiagram p) q)).1
  apply relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  rfl

end SerrePositivity.InfinityCategories
