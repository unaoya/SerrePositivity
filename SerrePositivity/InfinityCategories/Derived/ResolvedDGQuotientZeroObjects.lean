module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientNerve
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.Stable.ZeroDiagramComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.DGNerve.FullSubcategory

/-! # 平坦分解後の商による元の指定対象の整合的な零化

概要：元の nerve から平坦分解後の商への関手は、指定対象を実際の零対象へ送る。
方針：分解上の商射影との屋根比較の成分に沿って零性を移し、関手圏で零図式と比較する。
規約：分解の厳密な逆 dg 関手は仮定しない。使われ方：β3 の導来商の零化条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 指定対象の固定ラベルでの持ち上げは、平坦分解後の収縮集合に入る。 -/
def resolvedDGNullObject (b : P) : resolvedDGNullObjects A D P :=
  ⟨⟨b.val⟩, b.property⟩

/-- 平坦分解後の商の選ばれた零頂点。 -/
def resolvedDGQuotientZeroVertex (b : P) : ZeroVertex (resolvedDGQuotientNerve A D P) :=
  dgQuotientKilledZeroVertex A _ _ (resolvedDGNullObject A D P b)

/-- 元の指定対象の像は、平坦分解後の商で実際の零対象。 -/
lemma resolvedDGQuotientFunctor_kills (b : P) :
    IsZeroVertex (X := resolvedDGQuotientNerve A D P)
      ((resolvedDGQuotientFunctor A D P).app _ (Simplex.vertex b.val)) := by
  let x : DGCategoryCellResolution.Source A D := ⟨b.val⟩
  have he := FunctorIso.app (resolvedDGQuotientRoofIso A D P) (Simplex.vertex x)
  change VertexIso
    ((resolvedDGQuotientFunctor A D P).app _
      ((dgNerve.map (DGCategoryCellResolution.augmentation A D)).app _ (Simplex.vertex x)))
    ((resolvedDGQuotientProjection A D P).app _ (Simplex.vertex x)) at he
  rw [dgFunctorNerve_vertex] at he
  have hz := dgQuotientNerveProjection_kills A (DGCategoryCellResolution.Source A D)
    (resolvedDGNullObjects A D P) (resolvedDGNullObject A D P b)
  exact hz.of_vertexIso he.symm

/-- 元の指定充満部分圏から平坦商への制限関手。 -/
def resolvedDGQuotientNullFunctor :
    dgNerve A (DGFullSubcategory D P) ⟶ resolvedDGQuotientNerve A D P :=
  dgNerve.map (dgFullSubcategoryInclusion A D P) ≫ resolvedDGQuotientFunctor A D P

/-- 元の指定部分圏上の制限関手の値は全て零対象。 -/
lemma resolvedDGQuotientNullFunctor_pointwise_zero
    (k : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌) :
    IsZeroVertex (X := resolvedDGQuotientNerve A D P)
      ((resolvedDGQuotientNullFunctor A D P).app _ k) := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective k
  change IsZeroVertex (X := resolvedDGQuotientNerve A D P)
    ((resolvedDGQuotientFunctor A D P).app _
      ((dgNerve.map (dgFullSubcategoryInclusion A D P)).app _ (Simplex.vertex x)))
  rw [dgFunctorNerve_vertex]
  exact resolvedDGQuotientFunctor_kills A D P x

/-- 元の指定部分圏上の関手は、平坦商の零対象の定値関手と整合的に同型。 -/
def resolvedDGQuotientNullFunctorIsoZero (b : P) :
    FunctorIso (resolvedDGQuotientNullFunctor A D P)
      (SSet.const (resolvedDGQuotientZeroVertex A D P b).vertex) :=
  zeroDiagramConstantIso _ (resolvedDGQuotientNullFunctor_pointwise_zero A D P)
    (resolvedDGQuotientZeroVertex A D P b)

end SerrePositivity.InfinityCategories
