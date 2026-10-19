module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.DGNerve.FullSubcategory
public import SerrePositivity.InfinityCategories.Stable.ZeroDiagramComparison

/-! # dg 商の指定部分圏上での整合的な零化

概要：商包含を指定充満部分圏に制限すると、零対象の定値 ∞ 関手と同型になる。
方針：全ての頂点の実零対象性から、関手 ∞ 圏の終対象性による比較を作る。
規約：全図式の可逆二胞体を与える。局所化普遍性は別工程。使われ方：β3 の Verdier 列。
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

/-- 商包含の指定充満部分圏への制限。 -/
def dgQuotientNullFunctor : dgNerve A (DGFullSubcategory D P) ⟶ dgQuotientNerve A D P :=
  dgNerve.map ((dgFullSubcategoryInclusion A D P).comp (DGQuotient.inclusion A D P))

/-- 制限した関手は二つの実際の包含関手の合成。 -/
lemma dgQuotientNullFunctor_eq_comp : dgQuotientNullFunctor A D P =
    dgNerve.map (dgFullSubcategoryInclusion A D P) ≫ dgQuotientNerveProjection A D P :=
  dgNerve.map_comp _ _

/-- 指定部分圏上の制限関手の値は全て実際の零頂点。 -/
lemma dgQuotientNullFunctor_pointwise_zero (k : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌) :
    IsZeroVertex (X := dgQuotientNerve A D P)
      ((dgQuotientNullFunctor A D P).app _ k) := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective k
  change IsZeroVertex (X := dgQuotientNerve A D P)
    ((dgNerve.map _).app _ (Simplex.vertex x))
  rw [dgFunctorNerve_vertex]
  exact dgQuotientKilledVertex_isZero A D P x

/-- 指定部分圏上の制限は、零対象の定値関手と関手 ∞ 圏で同型。 -/
def dgQuotientNullFunctorIsoZero (b : P) :
    FunctorIso (dgQuotientNullFunctor A D P)
      (SSet.const (dgQuotientKilledZeroVertex A D P b).vertex) :=
  zeroDiagramConstantIso _ (dgQuotientNullFunctor_pointwise_zero A D P)
    (dgQuotientKilledZeroVertex A D P b)

end SerrePositivity.InfinityCategories
