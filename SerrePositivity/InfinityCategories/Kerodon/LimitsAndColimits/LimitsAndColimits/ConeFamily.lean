module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEquiv

/-!
概要：通常の錐の nerve から native な錐の族への比較射。
方針：図式を固定する射を fiber へ持ち上げ頂点の全単射を照合する。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：通常の錐の nerve を native な固定図式上の錐の族へ写す。
方針：図式を固定する比較射を fiber へ持ち上げる。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def nerveConeFamilyMap : nerve (Cone F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (nerveMap F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (nerve I) (nerve C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F))
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeFamilyUnderlying _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeFamilyUnderlying_fixed

/-- 概要：錐の族への比較射の零次成分は元の錐の表示に等しい。
方針：fiber の包含の後で関手頂点を照合する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeFamilyMap_vertex (c : Cone F) :
    (nerveConeFamilyMap (F := F)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv (nerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c) := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeFamilyUnderlying_vertex c

/-- 概要：錐の族への比較射は対象の上で全単射。
方針：nerve の頂点・通常の錐・join の錐の全単射を合成する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeFamilyMap_bijective_vertices :
    Function.Bijective ((nerveConeFamilyMap (F := F)).app (Opposite.op ⦋0⦌)) := by
  let e := (nerveEquiv (C := Cone F)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeEquiv (F := F)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv (nerveMap F)))
  have he : (fun s ↦ (nerveConeFamilyMap (F := F)).app (Opposite.op ⦋0⦌) s) = e := by
    funext s
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := Cone F)).symm.surjective s
    exact nerveConeFamilyMap_vertex c
  change Function.Bijective (fun s ↦ (nerveConeFamilyMap (F := F)).app (Opposite.op ⦋0⦌) s)
  rw [he]
  exact e.bijective

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
