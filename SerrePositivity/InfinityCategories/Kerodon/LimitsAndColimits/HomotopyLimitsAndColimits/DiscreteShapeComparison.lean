module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison

/-!
概要：IsDiscrete な任意の小圏の Bousfield–Kan 重みは厳密な終対象である。
方針：射から対象の等号を回収して各 over 圏を一点と示し、重みの終対象性をまとめる。
規約：Discrete J という表示を要求せず、反対圏の離散添字にもそのまま使う。
使われ方：Kerodon 7.5.4.1（Tag 03B6）・7.5.4.6（Tag 03BB）、HTT 4.2.4.1 の余積への双対化。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] [IsDiscrete I]

/-- 概要：離散な小圏の各 over 圏の対象は一意。
方針：各構造射から始点と固定終点の等号を得て対象の外延性を使う。
規約：圏同値でなく実際の等号を用いる。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、離散重みの厳密な計算。 -/
instance isDiscreteOver_subsingleton (i : I) : Subsingleton (Over i) where
  allEq a b := CostructuredArrow.obj_ext a b
    ((IsDiscrete.eq_of_hom a.hom).trans (IsDiscrete.eq_of_hom b.hom).symm)
    (Subsingleton.elim _ _)

/-- 概要：離散な小圏の各 over 圏は薄い。
方針：射の左成分の一意性で over 圏の射を比較する。
規約：対象の選択によらない全 Hom の一意性。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、重みの全単体の一意性。 -/
instance isDiscreteOver_isThin (i : I) : Quiver.IsThin (Over i) :=
  fun _ _ ↦ ⟨fun f g ↦ CostructuredArrow.hom_ext f g (Subsingleton.elim _ _)⟩

/-- 概要：離散な小圏の over 圏の nerve は全次数で高々一点。
方針：薄い圏の単体を各頂点で比較し、対象の一意性を使う。
規約：全ての次数に対する Subsingleton の instance。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、重みの厳密な終対象性。 -/
instance isDiscreteOverNerve_obj_subsingleton (i : I) (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((nerve (Over i)).obj n) where
  allEq _ _ := nerve.ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)

/-- 概要：離散な小圏の over 圏の nerve は単体集合の終対象。
方針：恒等射の頂点の定値写像を選び、全次数の一意性で普遍性を示す。
規約：非空な一点を明示し、単なる可縮性で代用しない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、離散重みの終対象。 -/
def isDiscreteOverNerve_isTerminal (i : I) : IsTerminal (nerve (Over i)) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ SSet.const (ComposableArrows.mk₀ (Over.mk (𝟙 i))))
    (fun _ _ ↦ by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact Subsingleton.elim _ _)

/-- 概要：任意の離散な小圏の Bousfield–Kan 重みは終対象。
方針：各 over 圏の nerve の終対象性を自然変換の普遍性にまとめる。
規約：空の添字と反対の離散添字を含む。
使われ方：Kerodon 7.5.4.1（Tag 03B6）・7.5.4.6（Tag 03BB）、積と余積の Hom 比較。 -/
def isDiscreteBousfieldKanWeight_isTerminal : IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj _ isDiscreteOverNerve_isTerminal

/-- 概要：任意の離散な小圏の strict 極限から end への標準比較は同型。
方針：終対象の重みの比較を標準極限錐に適用する。
規約：係数の Kan 性を仮定しない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、反対の離散添字上の極限の比較。 -/
instance bousfieldKanLimitComparison_isDiscrete_isIso (H : I ⥤ SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight _ isDiscreteBousfieldKanWeight_isTerminal
    (limit.cone H) (limit.isLimit H)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
