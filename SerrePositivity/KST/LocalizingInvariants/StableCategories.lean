module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

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

end SerrePositivity.KST.LocalizingInvariants
