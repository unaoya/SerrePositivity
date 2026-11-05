module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration

/-!
概要：K-5 の安定 ∞ 圏と、その間の完全関手の ∞ 圏。
方針：F3 の安定性を束ね、関手単体集合の完全な頂点の全部分複体を取る。
規約：Sp の安定性は使用しない。使われ方：抽象 Verdier 列と局所化不変量。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Verdier
open SerrePositivity.KST.LocalizingInvariants

/-- 小さい安定 quasicategory。冪等完備性は別条件であり、ここには含めない。 -/
structure StableCategory where
  obj : SSet.{u}
  isQuasicategory : Quasicategory obj
  isStable : @IsStable obj isQuasicategory

attribute [instance] StableCategory.isQuasicategory StableCategory.isStable

/-- 完全関手は F3 の零対象・cofiber 保存条件を満たす実際の単体的射。 -/
structure ExactMap (A B : StableCategory.{u}) where
  hom : A.obj ⟶ B.obj
  isExact : IsExactFunctor hom

attribute [instance] ExactMap.isExact

@[ext] lemma ExactMap.ext {A B : StableCategory.{u}} {F G : ExactMap A B}
    (h : F.hom = G.hom) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- 恒等・合成は F3 の完全関手の恒等・合成を継承する。 -/
instance stableCategory_category : Category.{u} StableCategory.{u} where
  Hom := ExactMap
  id A := ⟨𝟙 A.obj, inferInstance⟩
  comp F G := ⟨F.hom ≫ G.hom, inferInstance⟩
  id_comp F := ExactMap.ext (Category.id_comp F.hom)
  comp_id F := ExactMap.ext (Category.comp_id F.hom)
  assoc F G H := ExactMap.ext (Category.assoc F.hom G.hom H.hom)

/-- 関手 ∞ 圏の頂点が表す実関手の完全性。 -/
def IsExactVertex (A B : StableCategory.{u})
    (v : ((ihom A.obj).obj B.obj) _⦋0⦌) : Prop :=
  IsExactFunctor ((functorVertexEquiv A.obj B.obj).symm v)

/-- 完全関手と全ての自然変換からなる充満部分 ∞ 圏。 -/
def exactFunctors (A B : StableCategory.{u}) : ((ihom A.obj).obj B.obj).Subcomplex :=
  fullSubcomplexOnVertices _ (IsExactVertex A B)

instance exactFunctors_quasicategory (A B : StableCategory.{u}) :
    Quasicategory (exactFunctors A B : SSet.{u}) :=
  inferInstanceAs (Quasicategory
    (fullSubcomplexOnVertices _ (IsExactVertex A B) : SSet.{u}))

/-- 完全関手 ∞ 圏の対象は、束ねた完全関手と一対一に対応する。 -/
def exactFunctorVertexEquiv (A B : StableCategory.{u}) :
    ExactMap A B ≃ (exactFunctors A B : SSet.{u}) _⦋0⦌ where
  toFun F := ⟨functorVertex F.hom, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    change IsExactFunctor ((functorVertexEquiv A.obj B.obj).symm
      ((functorVertexEquiv A.obj B.obj) F.hom))
    rw [Equiv.symm_apply_apply]
    exact F.isExact⟩
  invFun v := ⟨(functorVertexEquiv A.obj B.obj).symm v.val,
    fullSubcomplexOnVertices_vertex v⟩
  left_inv F := ExactMap.ext ((functorVertexEquiv A.obj B.obj).symm_apply_apply F.hom)
  right_inv v := Subtype.ext ((functorVertexEquiv A.obj B.obj).apply_symm_apply v.val)

/-- 包含を後合成すると元の関手の頂点表示になる。 -/
lemma exactFunctorVertexEquiv_val {A B : StableCategory.{u}} (F : ExactMap A B) :
    (exactFunctorVertexEquiv A B F).val = functorVertex F.hom := rfl

/-- 完全性は関手 ∞ 圏の同型で移送される。 -/
lemma isExact_of_functorIso {A B : StableCategory.{u}} (F : ExactMap A B)
    {G : A.obj ⟶ B.obj} (e : FunctorIso F.hom G) : IsExactFunctor G :=
  isExactFunctor_of_functorIso e

end SerrePositivity.InfinityCategories.Stable.Verdier

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsExactVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsExactVertex := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsExactVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv_val := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv_val

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctors (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctors := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctors

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctors_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctors_quasicategory := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctors_quasicategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.isExact_of_functorIso := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.isExact_of_functorIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ext := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ext_iff := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.hom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.hom := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.hom

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.isExact (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.isExact := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.isExact

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.rec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isQuasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.isQuasicategory := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isQuasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isStable (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.isStable := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isStable

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.obj (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.obj := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.obj

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.rec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_5 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_6 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_5 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_6 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_7 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_8 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_9 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.stableCategory_category._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.mk.sizeOf_spec
