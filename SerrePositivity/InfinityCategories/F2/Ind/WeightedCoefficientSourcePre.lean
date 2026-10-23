module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientSourceComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UliftPrecomposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeakHomotopyPrecomposition

/-!
概要：元の係数評価の始点固定値写像は、必要な小さい Kan 標的への前合成で同値。
方針：同じ恒等 fiber の比較を消去し、同じ値 fiber 内の関手同型で移す。
規約：元の全評価の同じ制限を検査。使われ方：指定 native 係数余錐の評価判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)

/-- 標準側の同じ始点固定作用は、同じ恒等 fiber 上の同値から弱同値になる。 -/
lemma weightedCoefficientCanonicalSourceValue_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (weightedCoefficientCanonicalSourceValue F i x) := by
  have : KanComplex (vertexFiber (F.obj i).val.hom x) := vertexFiber_kanComplex _ _
  apply (twistedSourceElementsIdentityInclusion_isWeakHomotopyEquivalence
    (F.obj i).val.hom x).cancel_left
  have h := weightedCoefficientCanonicalSourceValue_identity_isQCatEquivalence F i x
  exact h.isWeakHomotopyEquivalence

/-- 元の全評価の係数・始点制限への前合成は、元の小さい Kan 標的で同値。 -/
lemma weightedCoefficientSourceValue_pre (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence ((pre (weightedCoefficientSourceValue F i x)).app Z) := by
  have h := pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence _
    (weightedCoefficientCanonicalSourceValue_isWeakHomotopyEquivalence F i x) Z
  have he := h.isQCatEquivalence.ofFunctorIso
    ((weightedCoefficientSourceValue_canonicalIso F i x).map_pre Z).symm
  exact he.isSimplicialHomotopyEquivalence

/-- 同じ値写像の持ち上げも、必要な持ち上げた小さい Kan 標的で前合成同値。 -/
lemma weightedCoefficientSourceValue_ulift_pre (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceValue F i x))).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) :=
  F2.ulift_pre_homotopyEquivalence _ (weightedCoefficientSourceValue_pre F i x Z)

end SerrePositivity.InfinityCategories.F2.Ind
