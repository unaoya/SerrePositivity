module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TerminalWeight
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
概要：離散添字の Bousfield–Kan 型の end は strict な積と同型。
方針：各 over 圏が対象も射も一意であることから重みの終対象性を示す。
規約：添字の有限性は不要で、空の添字も含む。∞ 圏の積との比較は後続の証明対象。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、7.5.4.6（Tag 03BB）、γ3c の有限積の計算部分。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {J : Type u}

/-- 概要：離散圏の各 over 圏の対象は一意。
方針：対象を定める射から始点が固定された終点に等しいことを得る。
規約：対象の一意性は等号であり、圏同値だけではない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、離散添字の重みの直接計算。 -/
instance discreteOver_subsingleton (i : Discrete J) : Subsingleton (Over i) where
  allEq a b := CostructuredArrow.obj_ext a b
    (Discrete.ext ((Discrete.eq_of_hom a.hom).trans (Discrete.eq_of_hom b.hom).symm))
    (Subsingleton.elim _ _)

/-- 概要：離散圏の各 over 圏は薄い。
方針：射は離散圏の射である左成分で決まる。
規約：全ての二対象間の射の一意性。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、重みの nerve の単体の一意性。 -/
instance discreteOver_isThin (i : Discrete J) : Quiver.IsThin (Over i) :=
  fun _ _ ↦ ⟨fun f g ↦ CostructuredArrow.hom_ext f g (Subsingleton.elim _ _)⟩

/-- 概要：離散圏の各 over 圏の nerve は各次数で高々一点。
方針：薄い圏の nerve の単体は頂点で決まり、over 圏の対象は一意である。
規約：全次数の単体について主張する。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、重みを忘れる射の同型性。 -/
instance discreteOverNerve_obj_subsingleton (i : Discrete J) (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((nerve (Over i)).obj n) where
  allEq _ _ := nerve.ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)

/-- 概要：離散圏の各 over 圏の nerve は終対象。
方針：恒等射の頂点を選び、全ての単体の一意性で射の一意性を示す。
規約：単に可縮という条件より強い厳密な終対象性。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、離散図式の Bousfield–Kan 重み。 -/
def discreteOverNerve_isTerminal (i : Discrete J) : IsTerminal (nerve (Over i)) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ SSet.const (ComposableArrows.mk₀ (Over.mk (𝟙 i))))
    (fun _ _ ↦ by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact Subsingleton.elim _ _)

/-- 概要：離散添字の Bousfield–Kan 重みは図式の圏の終対象。
方針：全ての成分の厳密な終対象性を自然変換にまとめる。
規約：添字が空の場合も同じ構成を使う。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、strict な積との比較。 -/
def discreteBousfieldKanWeight_isTerminal : IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Discrete J)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj _ discreteOverNerve_isTerminal

/-- 概要：離散図式の strict 極限から Bousfield–Kan 型の end への標準比較は同型。
方針：重みの終対象性を strict 極限錐に適用する。
規約：添字の有限性と各成分の Kan 性は不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、γ3c の積の標準比較射。 -/
instance bousfieldKanLimitComparison_discrete_isIso (H : Discrete J ⥤ SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight _ discreteBousfieldKanWeight_isTerminal
    (limit.cone H) (limit.isLimit H)

/-- 概要：厳密な同型である単体集合の射は実際の単体的ホモトピー逆を持つ。
方針：同型の逆射と、両合成が恒等であることによる定値ホモトピーを使う。
規約：始域と終域の Kan 性は不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、積の標準比較のホモトピー同値性。 -/
lemma homotopyEquivalence_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  refine ⟨inv f, ?_, ?_⟩
  · rw [IsIso.hom_inv_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))⟩
  · rw [IsIso.inv_hom_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 Y))⟩

/-- 概要：離散図式の標準比較は実際のホモトピー同値。
方針：構成した標準比較の厳密な同型性からホモトピー逆を得る。
規約：空積と任意の小さな積を含み、成分の Kan 性も不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、γ3c の有限積の κ_x。 -/
lemma bousfieldKanLimitComparison_discrete_homotopyEquivalence
    (H : Discrete J ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  homotopyEquivalence_of_isIso _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
