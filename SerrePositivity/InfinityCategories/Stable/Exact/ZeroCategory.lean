module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.UniqueTarget
end SerrePositivity.KST.LocalizingInvariants.UniqueTarget
namespace SerrePositivity.InfinityCategories.Stable.Exact
open SerrePositivity.KST.LocalizingInvariants

namespace UniqueTarget
open SerrePositivity.KST.LocalizingInvariants.UniqueTarget
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
  fun _n _b ↦ ⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _⟩

/-- 全ての実頂点は零対象。 -/
lemma zero (x : X _⦋0⦌) : IsZeroVertex x :=
  ⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible.isInitialVertex x, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible.isTerminalVertex x⟩

/-- slice の各次数にも唯一の錐がある。 -/
@[instance_reducible] def sliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((sliceOver p).obj n) where
  default := ⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _⟩
  uniq _a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _)

/-- coslice の各次数にも唯一の余錐がある。 -/
@[instance_reducible] def cosliceUnique {K : SSet.{u}} (p : K ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Unique ((sliceUnder p).obj n) where
  default := ⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _⟩
  uniq _a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _)

lemma limit {K : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c := by
  let : ∀ n, Unique ((sliceOver p).obj n) := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.sliceUnique p
  exact (_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible (X := sliceOver p)).isTerminalVertex c

lemma colimit {K : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) : IsColimitCone c := by
  let : ∀ n, Unique ((sliceUnder p).obj n) := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.cosliceUnique p
  exact (_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible (X := sliceUnder p)).isInitialVertex c

lemma pullback (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : IsPullbackSquare F :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.limit (pullbackCone F)

lemma pushout (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : IsPushoutSquare F :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.colimit (pushoutCocone F)

end UniqueTarget

private instance unitSimplexUnique (n : SimplexCategoryᵒᵖ) :
    Unique ((𝟙_ SSet.{u}).obj n) := inferInstanceAs (Unique PUnit)

/-- 一点の単体集合は零安定 ∞ 圏を与える。 -/
def zeroCategory : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u} where
  obj := 𝟙_ SSet.{u}
  isQuasicategory := by
    let : KanComplex (𝟙_ SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible.kanComplex
    infer_instance
  isStable := by
    let : KanComplex (𝟙_ SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible.kanComplex
    let : HasZeroVertex (𝟙_ SSet.{u}) :=
      ⟨⟨PUnit.unit, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.zero _⟩⟩
    let : HasFiniteLimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _⟩, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.limit _⟩⟩
    let : HasFiniteColimits (𝟙_ SSet.{u}) :=
      ⟨fun _p ↦ ⟨⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map _, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext _ _⟩, _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.colimit _⟩⟩
    exact isStable_of_finite_limits_colimits
      (fun F ↦ ⟨fun _ ↦ _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.pushout F, fun _ ↦ _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.pullback F⟩)

private instance zeroSimplexUnique : ∀ n : SimplexCategoryᵒᵖ,
    Unique (_root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory.{u}.obj.obj n) := fun n ↦ unitSimplexUnique n

lemma zeroCategory_isZero : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory.{u} := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.zero

/-- 任意の安定圏から零安定圏への実際の完全関手。 -/
def toZeroCategory (A : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory.{u} := by
  let : ∀ n : SimplexCategoryᵒᵖ, Unique ((𝟙_ SSet.{u}).obj n) :=
    fun _ ↦ inferInstanceAs (Unique PUnit)
  exact {
    hom := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map (X := (𝟙_ SSet.{u})) A.obj
    isExact := {
      preservesZero := fun _x _ ↦ _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.zero (X := (𝟙_ SSet.{u})) _
      preservesCofiber := fun _t _ ↦ _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.pushout (X := (𝟙_ SSet.{u})) _ } }

end SerrePositivity.InfinityCategories.Stable.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.toZeroCategory := _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.zeroCategory := _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.zeroCategory_isZero := _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory_isZero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.colimit := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.colimit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.contractible := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.contractible

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.cosliceUnique (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.cosliceUnique := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.cosliceUnique

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.hom_ext := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.hom_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.limit := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.limit

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.map := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.pullback := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.pullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.pushout := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.pushout

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.sliceUnique (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.sliceUnique := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.sliceUnique

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.zero := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory._aux_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.toZeroCategory._aux_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory._aux_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.toZeroCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.toZeroCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.zeroCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.zeroCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.cosliceUnique._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.cosliceUnique._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.cosliceUnique._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.cosliceUnique._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.map._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.map._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.sliceUnique._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.sliceUnique._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.UniqueTarget.sliceUnique._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.UniqueTarget.sliceUnique._proof_2
