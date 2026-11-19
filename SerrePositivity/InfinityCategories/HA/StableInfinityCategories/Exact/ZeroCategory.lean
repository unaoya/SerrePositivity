module


public meta import SerrePositivity.Util.Citation
public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-!
概要：一点の単体集合による実際の零安定 ∞ 圏。
方針：各次数で唯一の単体を持つ標的の全ての錐・余錐の普遍性を直接充填で示す。
規約：安定性の入力構造を仮定しない。使われ方：Verdier 列の coherent な零角。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.UniqueTarget
end SerrePositivity.KST.LocalizingInvariants.UniqueTarget
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

namespace UniqueTarget
open _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget
variable {X : SSet.{u}} [∀ n, Unique (X.obj n)]

/-- 次数ごとの唯一の単体による標準射。 -/
def map (A : SSet.{u}) : A ⟶ X where
  app _ := ↾fun _ ↦ default
  naturality {_ _} _ := by
    apply ConcreteCategory.hom_ext
    intro _a
    exact Subsingleton.elim _ _

lemma hom_ext {A : SSet.{u}} (f g : A ⟶ X) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro _a
  exact Subsingleton.elim _ _

/-- 唯一の標的では全ての境界が充填される。 -/
lemma contractible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X :=
  fun _n _b ↦ ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _⟩

/-- 全ての実頂点は零対象。 -/
lemma zero (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex x :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible.isInitialVertex x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible.isTerminalVertex x⟩

/-- slice の各次数にも唯一の錐がある。 -/
@[instance_reducible] def sliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).obj n) where
  default := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _⟩
  uniq _a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _)

/-- coslice の各次数にも唯一の余錐がある。 -/
@[instance_reducible] def cosliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).obj n) where
  default := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _⟩
  uniq _a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _)

lemma limit {K : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  let : ∀ n, Unique ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).obj n) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.sliceUnique p
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)).isTerminalVertex c

lemma colimit {K : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  let : ∀ n, Unique ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).obj n) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.cosliceUnique p
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)).isInitialVertex c

lemma pullback (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.limit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)

lemma pushout (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)

end UniqueTarget

private instance unitSimplexUnique (n : SimplexCategoryᵒᵖ) :
    Unique ((𝟙_ SSet.{u}).obj n) := inferInstanceAs (Unique PUnit)

/-- 一点の単体集合は零安定 ∞ 圏を与える。 -/
def zeroCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  obj := 𝟙_ SSet.{u}
  isQuasicategory := by
    let : KanComplex (𝟙_ SSet.{u}) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible.kanComplex
    infer_instance
  isStable := by
    let : KanComplex (𝟙_ SSet.{u}) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.contractible.kanComplex
    let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (𝟙_ SSet.{u}) :=
      ⟨⟨PUnit.unit, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.zero _⟩⟩
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _⟩, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.limit _⟩⟩
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.hom_ext _ _⟩, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.colimit _⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_finite_limits_colimits
      (fun F ↦ ⟨fun _ ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.pushout F, fun _ ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.pullback F⟩)

private instance zeroSimplexUnique : ∀ n : SimplexCategoryᵒᵖ,
    Unique (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u}.obj.obj n) := fun n ↦ unitSimplexUnique n

lemma zeroCategory_isZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.zero

/-- 任意の安定圏から零安定圏への実際の完全関手。 -/
def toZeroCategory (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := by
  let : ∀ n : SimplexCategoryᵒᵖ, Unique ((𝟙_ SSet.{u}).obj n) :=
    fun _ ↦ inferInstanceAs (Unique PUnit)
  exact {
    hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.map (X := (𝟙_ SSet.{u})) A.obj
    isExact := {
      preservesZero := fun _x _ ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.zero (X := (𝟙_ SSet.{u})) _
      preservesCofiber := fun _t _ ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.UniqueTarget.pushout (X := (𝟙_ SSet.{u})) _ } }

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
























/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.4.3" (partial := special) "仮定：二つの安定準圏（Lean が強い：任意の族でなく二項積を零 ∞ 圏への完全関手の引き戻しに特殊化）。結論：零 ∞ 圏上の引き戻しは安定。任意族の積の安定性と成分ごとの完全性の判定は型にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory
