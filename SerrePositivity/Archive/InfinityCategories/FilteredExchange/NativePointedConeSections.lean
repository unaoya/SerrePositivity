module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedConeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionRestrictionCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily

/-!
概要：始点を固定した native 全錐の持ち上げを、同じ図式の切断の族へ送る。
方針：全持ち上げを相対 curry し、始点の left anodyne 制限で同値性を検出する。
規約：指定した全錐と始点族を保持。使われ方：元の極限性から fiber 比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
local notation "V" => join Δ[0] K
local notation "j" => joinInl Δ[0] K

/-- 全錐の同じ持ち上げを、全図式上の切断の族に表示する。 -/
def nativePointedConeFullSections : A ⟶
    HomotopyLimits.coherentConeSectionSpace c.val pointSpaceVertex.{u} :=
  relativeFunctorCurry (nativePointedConeLift c s hs)
    (nativePointedConeLift_projection c s hs)

/-- 始点族の相対 curry。底は全錐の頂点への実際の制限そのもの。 -/
def nativePointedConeInitialSections : A ⟶
    relativeFunctorSpace pointedSpaceProjection (j ≫ c.val) :=
  relativeFunctorCurry (snd (Δ[0] : SSet.{u + 1}) A ≫ s)
    (nativePointedCone_initial c s hs)

/-- 始点への制限は、元の全始点族を全次数で厳密に回収する。 -/
lemma nativePointedConeFullSections_initial :
    nativePointedConeFullSections c s hs ≫ relativeFunctorPre pointedSpaceProjection c.val j =
      nativePointedConeInitialSections c s hs := by
  apply relativeFunctorUncurry_injective pointedSpaceProjection (j ≫ c.val)
  rw [relativeFunctorUncurry_pre, nativePointedConeFullSections,
    nativePointedConeInitialSections, relativeFunctorUncurry_curry,
    relativeFunctorUncurry_curry, nativePointedConeLift_initial]

/-- 一点で評価すると、元の pointed 始点族を厳密に回収する。 -/
lemma nativePointedConeInitialSections_evaluate_ι :
    nativePointedConeInitialSections c s hs ≫
      relativeFunctorEvaluate pointedSpaceProjection (j ≫ c.val) (stdSimplex.obj₀Equiv.symm 0) ≫
      vertexFiberι pointedSpaceProjection
        ((j ≫ c.val).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) = s := by
  rw [relativeFunctorEvaluate_ι]
  change curry (snd Δ[0] A ≫ s) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = s
  rw [curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd, Category.id_comp]

variable [Quasicategory A]

/-- 全錐の切断族の同値性は、元の始点族の相対表示の同値性と同値。 -/
lemma nativePointedConeFullSections_isQCatEquivalence_iff :
    IsQCatEquivalence (nativePointedConeFullSections c s hs) ↔
      IsQCatEquivalence (nativePointedConeInitialSections c s hs) := by
  have := relativeFunctorPre_trivialKanFibration pointedSpaceProjection c.val j
    (joinPoint_inl_leftAnodyne K)
  have he := isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorPre pointedSpaceProjection c.val j)
  constructor
  · intro h
    rw [← nativePointedConeFullSections_initial c s hs]
    exact h.comp he
  · intro h
    apply he.cancel_right
    rwa [nativePointedConeFullSections_initial]

/-- 元の全錐の図式部分への制限が定める、元の図式上の切断族。 -/
def nativePointedConeSections : A ⟶
    HomotopyLimits.coherentConeSectionSpace d pointSpaceVertex.{u} :=
  nativePointedConeFullSections c s hs ≫
    HomotopyLimits.coneSectionRestriction c pointSpaceVertex.{u}

omit [Quasicategory A] in
/-- 図式上の切断族の展開は、元の全 pointed 錐の右因子への厳密な制限。 -/
lemma nativePointedConeSections_uncurry :
    relativeFunctorUncurry (nativePointedConeSections c s hs) =
      (joinInr Δ[0] K ▷ A) ≫ nativePointedConeLift c s hs := by
  unfold nativePointedConeSections HomotopyLimits.coneSectionRestriction
  rw [← Category.assoc, HomotopyLimits.relativeFunctorUncurry_eqToHom,
    relativeFunctorUncurry_pre, nativePointedConeFullSections, relativeFunctorUncurry_curry]
  exact c.property

/-- native 極限性を実際の全持ち上げの切断族へ適用する。 -/
lemma nativePointedConeSections_isQCatEquivalence (hc : IsLimitCone c)
    (h : IsQCatEquivalence (nativePointedConeInitialSections c s hs)) :
    IsQCatEquivalence (nativePointedConeSections c s hs) :=
  ((nativePointedConeFullSections_isQCatEquivalence_iff c s hs).mpr h).comp
    (((HomotopyLimits.isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc
      pointSpaceVertex.{u}).isQCatEquivalence)

end SerrePositivity.InfinityCategories.F2
