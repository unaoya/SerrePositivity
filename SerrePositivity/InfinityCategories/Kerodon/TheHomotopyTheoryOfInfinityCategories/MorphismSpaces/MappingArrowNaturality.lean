module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowCriterion

/-!
概要：coherent な比較と構成した随伴の比較との整合と二変数自然性。
方針：抽出単位を回収し、標準 pinched 比較を介して既存の随伴比較へ移す。
規約：各点の同値性だけを仮定し、自然性は帰結として公開する。
使われ方：B1 の具体的な coherent 対応の存在判定と対象変数の自然性の照合。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G)

/-- 概要：元の pinched 比較は構成した随伴の比較と同型。
方針：標準比較との同型と、抽出単位の回収を合成する。
規約：h Fun の同型。使われ方：元の比較を保持した存在判定の整合。 -/
def pinchedMapAdjunctionIso (hq : q.IsPointwiseEquivalence) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q.pinchedMap x y) ((q.adjunctionOfPointwiseEquivalence hq).pinchedMap x y) := by
  have h := (q.adjunctionOfPointwiseEquivalence hq).unitPinchedMapIso x y
  rw [q.adjunctionOfPointwiseEquivalence_unitHom hq] at h
  exact q.pinchedMap_unitIso x y ≪≫ h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pinchedMapAdjunctionIso)


/-- 概要：各点で同値な coherent 比較は標的変数に自然。
方針：構成した随伴の自然性を元の比較との同型で移す。
規約：hY の任意の射に対する h Fun の同型。
使われ方：pinched 写像空間の自然なホモトピー同値の標的自然性。 -/
def pinchedMapNaturalityRightIso (hq : q.IsPointwiseEquivalence)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ q.pinchedMap x y')
      (q.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose x ((hoFunctor.map G).toFunctor.map δ)) :=
  (q.pinchedMapAdjunctionIso hq x y').precomp _ ≪≫
    (q.adjunctionOfPointwiseEquivalence hq).pinchedMapNaturalityRightIso x δ ≪≫
      ((q.pinchedMapAdjunctionIso hq x y).postcomp _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pinchedMapNaturalityRightIso)


/-- 概要：各点で同値な coherent 比較は始域変数に反変に自然。
方針：構成した随伴の自然性を元の比較との同型で移す。
規約：hX の任意の射に対する h Fun の同型。
使われ方：pinched 写像空間の自然なホモトピー同値の始域自然性。 -/
def pinchedMapNaturalityLeftIso (hq : q.IsPointwiseEquivalence)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ q.pinchedMap x' y)
      (q.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (G.app (Opposite.op ⦋0⦌) y) γ) :=
  (q.pinchedMapAdjunctionIso hq x' y).precomp _ ≪≫
    (q.adjunctionOfPointwiseEquivalence hq).pinchedMapNaturalityLeftIso y γ ≪≫
      ((q.pinchedMapAdjunctionIso hq x y).postcomp _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pinchedMapNaturalityLeftIso)


/-- 概要：標的変数の自然性を実際のホモトピーで述べる。
方針：h Fun の自然性同型の辺代表を取る。
規約：各点の同値性のみを追加仮定とする。使われ方：自然性の可換正方形。 -/
lemma pinchedMap_naturality_right (hq : q.IsPointwiseEquivalence)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ q.pinchedMap x y')
      (q.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose x ((hoFunctor.map G).toFunctor.map δ))) :=
  ⟨(q.pinchedMapNaturalityRightIso hq x δ).simplicialHomotopy⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pinchedMap_naturality_right)


/-- 概要：始域変数の自然性を実際のホモトピーで述べる。
方針：h Fun の自然性同型の辺代表を取る。
規約：各点の同値性のみを追加仮定とする。使われ方：反変な可換正方形。 -/
lemma pinchedMap_naturality_left (hq : q.IsPointwiseEquivalence)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ q.pinchedMap x' y)
      (q.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (G.app (Opposite.op ⦋0⦌) y) γ)) :=
  ⟨(q.pinchedMapNaturalityLeftIso hq y γ).simplicialHomotopy⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pinchedMap_naturality_left)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
