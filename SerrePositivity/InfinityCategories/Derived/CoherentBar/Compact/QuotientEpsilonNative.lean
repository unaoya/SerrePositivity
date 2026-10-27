module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCriterion
public import SerrePositivity.DifferentialGraded.Quotient.FunctorLaws
public import SerrePositivity.KST.SConstruction.DGFunctorNativeCompositionCoherence

/-!
概要：固定 ε 整合商作用の native core 上の全単体写像と単位保存。
方針：実 dg 関手の nerve と core 制限を取り、正本恒等関手の厳密等号を使う。
規約：native Hom を頂点集合に置き換えない。
使われ方：商作用の全単体の横の単位則。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory Opposite Simplicial SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D : Type v) [DGCategory R C] [DGCategory R D] [Small.{u} C] [Small.{u} D]
  (S : Set C) (T : Set D)

/-- ε 整合関手の全 native Hom 空間。 -/
def quotientEpsilonNativeSpace : SSet.{max u v} :=
  quasicategoryCore (dgNerve R (NullPreservingFunctorsε R C D S T))

/-- 固定 ε 商作用の全単体写像。 -/
def quotientEpsilonNativeMap :
    quotientEpsilonNativeSpace R C D S T ⟶
      dgFunctorNativeMappingSpace R (DGQuotient.QuotientObject C S)
        (DGQuotient.QuotientObject D T) :=
  quasicategoryCoreMap (dgNerve.map (quotientInputFunctor R C D S T))

omit [DGCategory R D] [Small.{u} D] in
/-- 元の恒等関手は同じ null 集合を保存する。 -/
def quotientEpsilonUnitObject : NullPreservingFunctorsε R C C S S :=
  ⟨DGFunctor.id C, fun _ hx => hx⟩

omit [DGCategory R D] [Small.{u} D] in
/-- ε 整合関手の native 空間の単位射。 -/
def quotientEpsilonNativeUnit : 𝟙_ SSet.{max u v} ⟶ quotientEpsilonNativeSpace R C C S S :=
  (SSet.unitHomEquiv _).symm
    ⟨DGNerve.Simplex.vertex (quotientEpsilonUnitObject R C S), quasicategoryCore_vertex _⟩

omit [DGCategory R D] [Small.{u} D] in
/-- 正本商作用は、単位射を全単体で厳密に保つ。 -/
lemma quotientEpsilonNativeMap_unit :
    quotientEpsilonNativeUnit R C S ≫ quotientEpsilonNativeMap R C C S S =
      dgFunctorNativeIdentity R (DGQuotient.QuotientObject C S) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  apply DGNerve.Simplex.vertexEquiv.injective
  exact DGQuotient.quotientDGFunctor_id R C S

end SerrePositivity.InfinityCategories
