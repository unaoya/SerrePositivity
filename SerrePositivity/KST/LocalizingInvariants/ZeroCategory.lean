module

public import SerrePositivity.KST.LocalizingInvariants.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Core.ContractibleKan

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace UniqueTarget
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
lemma contractible : IsContractibleKan X :=
  fun _n _b ↦ ⟨map _, hom_ext _ _⟩

/-- 全ての実頂点は零対象。 -/
lemma zero (x : X _⦋0⦌) : IsZeroVertex x :=
  ⟨contractible.isInitialVertex x, contractible.isTerminalVertex x⟩

/-- slice の各次数にも唯一の錐がある。 -/
@[instance_reducible] def sliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((sliceOver p).obj n) where
  default := ⟨map _, hom_ext _ _⟩
  uniq _a := Subtype.ext (hom_ext _ _)

/-- coslice の各次数にも唯一の余錐がある。 -/
@[instance_reducible] def cosliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((sliceUnder p).obj n) where
  default := ⟨map _, hom_ext _ _⟩
  uniq _a := Subtype.ext (hom_ext _ _)

lemma limit {K : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c := by
  let : ∀ n, Unique ((sliceOver p).obj n) := sliceUnique p
  exact (contractible (X := sliceOver p)).isTerminalVertex c

lemma colimit {K : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) : IsColimitCone c := by
  let : ∀ n, Unique ((sliceUnder p).obj n) := cosliceUnique p
  exact (contractible (X := sliceUnder p)).isInitialVertex c

lemma pullback (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : IsPullbackSquare F :=
  limit (pullbackCone F)

lemma pushout (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : IsPushoutSquare F :=
  colimit (pushoutCocone F)

end UniqueTarget

private instance unitSimplexUnique (n : SimplexCategoryᵒᵖ) :
    Unique ((𝟙_ SSet.{u}).obj n) := inferInstanceAs (Unique PUnit)

/-- 一点の単体集合は零安定 ∞ 圏を与える。 -/
def zeroCategory : StableCategory.{u} where
  obj := 𝟙_ SSet.{u}
  isQuasicategory := by
    let : KanComplex (𝟙_ SSet.{u}) := UniqueTarget.contractible.kanComplex
    infer_instance
  isStable := by
    let : KanComplex (𝟙_ SSet.{u}) := UniqueTarget.contractible.kanComplex
    let : HasZeroVertex (𝟙_ SSet.{u}) :=
      ⟨⟨PUnit.unit, UniqueTarget.zero _⟩⟩
    let : HasFiniteLimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨UniqueTarget.map _, UniqueTarget.hom_ext _ _⟩, UniqueTarget.limit _⟩⟩
    let : HasFiniteColimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨UniqueTarget.map _, UniqueTarget.hom_ext _ _⟩, UniqueTarget.colimit _⟩⟩
    exact isStable_of_finite_limits_colimits
      (fun F ↦ ⟨fun _ ↦ UniqueTarget.pushout F, fun _ ↦ UniqueTarget.pullback F⟩)

private instance zeroSimplexUnique : ∀ n : SimplexCategoryᵒᵖ,
    Unique (zeroCategory.{u}.obj.obj n) := fun n ↦ unitSimplexUnique n

lemma zeroCategory_isZero : IsZeroCategory zeroCategory.{u} := UniqueTarget.zero

/-- 任意の安定圏から零安定圏への実際の完全関手。 -/
def toZeroCategory (A : StableCategory.{u}) : ExactMap A zeroCategory.{u} := by
  let : ∀ n : SimplexCategoryᵒᵖ, Unique ((𝟙_ SSet.{u}).obj n) :=
    fun _ ↦ inferInstanceAs (Unique PUnit)
  exact {
    hom := UniqueTarget.map (X := (𝟙_ SSet.{u})) A.obj
    isExact := {
      preservesZero := fun _x _ ↦ UniqueTarget.zero (X := (𝟙_ SSet.{u})) _
      preservesCofiber := fun _t _ ↦ UniqueTarget.pushout (X := (𝟙_ SSet.{u})) _ } }

end SerrePositivity.KST.LocalizingInvariants
