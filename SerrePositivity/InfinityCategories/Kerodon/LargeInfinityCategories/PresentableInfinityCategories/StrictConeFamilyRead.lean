module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalFilteredKanCones
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：WithInitial との積上の一つの strict Kan 図式から、元の脚を持つ錐族を読み戻す。
方針：共同図式の curry と新しい始対象での評価を使い、錐の全脚を通常の極限へ持ち上げる。
規約：個々の段階で錐を選び直さず、共同図式の射をそのまま保持する。
使われ方：coherent な錐族の共同 strictification を native な極限保存へ接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  (D : J × WithInitial I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})

/-- 元の共同図式の、元の図式部分への制限。 -/
def strictConeFamilyDiagram : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Functor.curry.obj D ⋙
    (Functor.whiskeringLeft I (WithInitial I) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj WithInitial.incl

/-- 元の共同図式の、新しい始対象における頂点族。 -/
def strictConeFamilyApex : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Functor.curry.obj D ⋙ (evaluation (WithInitial I) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj WithInitial.star

/-- 各段階の元の錐は、共同図式の始対象からの射を脚に持つ。 -/
def strictConeFamilyStage (j : J) : Cone ((strictConeFamilyDiagram D).obj j) where
  pt := (strictConeFamilyApex D).obj j
  π := (WithInitial.mkCommaObject ((Functor.curry.obj D).obj j)).hom

/-- 元の全脚を一つの自然変換として通常の極限へ持ち上げる。 -/
def strictConeFamilyLimitMap :
    strictConeFamilyApex D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying (strictConeFamilyDiagram D) ⋙ lim where
  app j := limit.lift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (strictConeFamilyStage D j))
  naturality j k f := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc]
    erw [limit.lift_π, limit.map_π, limit.lift_π_assoc]
    exact (((Functor.curry.obj D).map f).naturality
      (WithInitial.starInitial.to (WithInitial.of i))).symm

/-- 読み戻した持ち上げの各射影は、元の段階錐の脚そのもの。 -/
@[reassoc] lemma strictConeFamilyLimitMap_π (j : J) (i : I) :
    (strictConeFamilyLimitMap D).app j ≫
      limit.π ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying (strictConeFamilyDiagram D)).obj j) i =
        (strictConeFamilyStage D j).π.app i :=
  limit.lift_π _ i

/-- 既存の極限保存の界面に渡す段階錐は、読み戻した元の錐と厳密に一致する。 -/
lemma strictConeFamilyStage_recovered (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanConeStage (strictConeFamilyDiagram D) (strictConeFamilyApex D)
      (strictConeFamilyLimitMap D) j = strictConeFamilyStage D j := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanConeStage strictConeFamilyStage _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeStage
  congr 1
  apply NatTrans.ext
  funext i
  exact strictConeFamilyLimitMap_π D j i

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 同じ共同図式から読み戻した native 極限錐族の余極限も native な極限錐。 -/
lemma strictConeFamilyColimit_isLimit
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (D : J × WithInitial I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (hc : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (strictConeFamilyStage D j))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanConeColimit (strictConeFamilyDiagram D) (strictConeFamilyApex D)
        (strictConeFamilyLimitMap D))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanConeColimit_isLimit h I hI J
  intro j
  rw [strictConeFamilyStage_recovered]
  exact hc j

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
