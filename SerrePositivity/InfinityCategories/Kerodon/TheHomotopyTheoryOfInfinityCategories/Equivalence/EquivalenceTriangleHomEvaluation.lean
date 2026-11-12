module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTriangleFaceEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostEquivalence

/-!
概要：同じ可逆三角形の Hom の各頂点・各面への射影は同値。
方針：元の評価と元の面の充満忠実性を、そのまま区間 Hom の作用へ移す。
規約：二つの元の三角形と全 Hom の族を保持する。
使われ方：元の比較 span の三角形による合成則。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 同じ可逆三角形の全ての頂点評価は同値。 -/
lemma equivalenceTriangleEvaluation_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation Y i) := by
  by_cases h₀ : i = 0
  · subst i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation_zero_isQCatEquivalence Y
  by_cases h₁ : i = 1
  · subst i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation_one_isQCatEquivalence Y
  have h₂ : i = 2 := Fin.ext (by
    have hlt := i.isLt
    have hn₀ : i.val ≠ 0 := fun h ↦ h₀ (Fin.ext h)
    have hn₁ : i.val ≠ 1 := fun h ↦ h₁ (Fin.ext h)
    omega)
  subst i
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace_isQCatEquivalence Y 1).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1))
  have hi : (1 : Fin 3).succAbove (1 : Fin 2) = 2 := by decide
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace_endpoint, hi] using h

/-- 元の二つの可逆三角形の同じ Hom を指定した頂点で評価する。 -/
def equivalenceTriangleHomEvaluation (Y : SSet.{u}) (i : Fin 3)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation Y i).app _ x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation Y i).app _ y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleEvaluation Y i) x y

/-- 同じ Hom の指定した頂点への射影は同値。 -/
lemma equivalenceTriangleHomEvaluation_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] (i : Fin 3)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (equivalenceTriangleHomEvaluation Y i x y) :=
  (equivalenceTriangleEvaluation_isQCatEquivalence Y i).isFullyFaithful
    |>.intervalMappingPost_isQCatEquivalence x y

/-- 元の二つの可逆三角形の同じ Hom を指定した面へ制限する。 -/
def equivalenceTriangleHomFace (Y : SSet.{u}) (i : Fin 3)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace Y i).app _ x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace Y i).app _ y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace Y i) x y

/-- 同じ Hom の指定した面への射影は同値。 -/
lemma equivalenceTriangleHomFace_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] (i : Fin 3)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (equivalenceTriangleHomFace Y i x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleFace_isQCatEquivalence Y i).isFullyFaithful
    |>.intervalMappingPost_isQCatEquivalence x y

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
