module
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence

/-! # 厳密 dg 入力の通常の圏
概要：dg 圏を束ね、厳密 dg 関手を射とする通常の入力圏を構成する。
方針：全 Hom 複体上の関手の等号で圏の法則を与える。
規約：単体的写像空間やその豊穣を省略した完成とは数えない。使われ方：Perf の零単体作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded

/-- 固定した係数環上の dg 圏の対象型と豊穣構造。 -/
structure BundledDGCategory (A : Type u) [CommRing A] where
  carrier : Type v
  enrichment : DGCategory A carrier

variable (A : Type u) [CommRing A]

instance bundledDGCategoryCoeSort : CoeSort (BundledDGCategory.{u, v} A) (Type v) :=
  ⟨BundledDGCategory.carrier⟩

instance bundledDGCategoryEnrichment (C : BundledDGCategory A) : DGCategory A C := C.enrichment

/-- 任意の dg 圏を対象宇宙を変えずに束ねる。 -/
def bundledDGCategoryOf (C : Type v) [DGCategory A C] : BundledDGCategory A :=
  ⟨C, inferInstance⟩

/-- 厳密 dg 関手を射とする圏。 -/
instance bundledDGCategoryCategory : Category (BundledDGCategory.{u, v} A) where
  Hom C D := DGFunctor A C D
  id C := DGFunctor.id C
  comp F G := F.comp G
  id_comp := strictDGFunctor_id_comp
  comp_id := strictDGFunctor_comp_id
  assoc := strictDGFunctor_comp_assoc

/-- 小さい入力の対象型・豊穣構造・小ささの証拠を保持する束。 -/
structure SmallBundledDGCategory (A : Type u) [CommRing A] where
  carrier : Type v
  enrichment : DGCategory A carrier
  small : Small.{u} carrier

instance smallBundledDGCategoryCoeSort : CoeSort (SmallBundledDGCategory.{u, v} A) (Type v) :=
  ⟨SmallBundledDGCategory.carrier⟩

instance smallBundledDGCategoryEnrichment (C : SmallBundledDGCategory A) : DGCategory A C :=
  C.enrichment

instance smallBundledDGCategorySmall (C : SmallBundledDGCategory A) : Small.{u} C := C.small

/-- 元の小さい dg 圏を、同じ対象宇宙の入力に束ねる。 -/
def smallBundledDGCategoryOf (C : Type v) [DGCategory A C] [Small.{u} C] :
    SmallBundledDGCategory A := ⟨C, inferInstance, inferInstance⟩

/-- 小さい厳密 dg 入力の通常の圏。射を準同値に局所化しない。 -/
instance smallBundledDGCategoryCategory : Category (SmallBundledDGCategory.{u, v} A) where
  Hom C D := DGFunctor A C D
  id C := DGFunctor.id C
  comp F G := F.comp G
  id_comp := strictDGFunctor_id_comp
  comp_id := strictDGFunctor_comp_id
  assoc := strictDGFunctor_comp_assoc

end SerrePositivity.KST.SConstruction
