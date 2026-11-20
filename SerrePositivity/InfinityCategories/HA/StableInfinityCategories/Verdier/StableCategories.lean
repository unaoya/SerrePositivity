module


public meta import SerrePositivity.Util.Citation
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




























































/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Def 2.12"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
