module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 小さい安定 quasicategory。冪等完備性は別条件であり、ここには含めない。 -/
structure StableCategory where
  obj : SSet.{u}
  isQuasicategory : Quasicategory obj
  isStable : @_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable obj isQuasicategory

attribute [instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isQuasicategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isStable

/-- 完全関手は F3 の零対象・cofiber 保存条件を満たす実際の単体的射。 -/
structure ExactMap (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) where
  hom : A.obj ⟶ B.obj
  isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor hom

attribute [instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.isExact

@[ext] lemma ExactMap.ext {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B}
    (h : F.hom = G.hom) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- 恒等・合成は F3 の完全関手の恒等・合成を継承する。 -/
instance stableCategory_category : Category.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  Hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
  id A := ⟨𝟙 A.obj, inferInstance⟩
  comp F G := ⟨F.hom ≫ G.hom, inferInstance⟩
  id_comp F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (Category.id_comp F.hom)
  comp_id F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (Category.comp_id F.hom)
  assoc F G H := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (Category.assoc F.hom G.hom H.hom)

/-- 関手 ∞ 圏の頂点が表す実関手の完全性。 -/
def IsExactVertex (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (v : ((ihom A.obj).obj B.obj) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm v)

/-- 完全関手と全ての自然変換からなる充満部分 ∞ 圏。 -/
def exactFunctors (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : ((ihom A.obj).obj B.obj).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A B)

instance exactFunctors_quasicategory (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A B) : SSet.{u}))

/-- 完全関手 ∞ 圏の対象は、束ねた完全関手と一対一に対応する。 -/
def exactFunctorVertexEquiv (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B ≃ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) _⦋0⦌ where
  toFun F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj) F.hom))
    rw [Equiv.symm_apply_apply]
    exact F.isExact⟩
  invFun v := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm v.val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v⟩
  left_inv F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm_apply_apply F.hom)
  right_inv v := Subtype.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).apply_symm_apply v.val)

/-- 包含を後合成すると元の関手の頂点表示になる。 -/
lemma exactFunctorVertexEquiv_val {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B F).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom := rfl

/-- 完全性は関手 ∞ 圏の同型で移送される。 -/
lemma isExact_of_functorIso {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    {G : A.obj ⟶ B.obj} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso e

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsExactVertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv_val := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv_val

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctors := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctors_quasicategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors_quasicategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.isExact_of_functorIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.isExact_of_functorIso

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ext := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.ext_iff := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.isExact (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.isExact := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.isExact

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isQuasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.isQuasicategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isQuasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isStable (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.isStable := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.isStable

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.obj (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.obj

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_4 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_5 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactFunctorVertexEquiv._proof_6 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_4 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_5 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_6 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_7 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_8 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_category._proof_9 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.stableCategory_category._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ExactMap.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableCategory.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.mk.sizeOf_spec
