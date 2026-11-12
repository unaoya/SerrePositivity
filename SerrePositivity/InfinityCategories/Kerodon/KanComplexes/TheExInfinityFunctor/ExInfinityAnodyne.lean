module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnitAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex∞ の単位の anodyne 性

概要：Ex の反復列を anodyne 拡張の順序合成とし、その余極限への単位の anodyne 性を示す。
方針：各遷移は本レーンで証明した Ex の単位であり、自然数添字の合成の閉性を使う。
規約：Moss 2020 Corollary 30。Kan 性の主張はこの定理に含めない。
使われ方：有限極限を保つ Kan 置換に向けた単位の検証。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits

/--
概要：Ex∞ への単位は Ex の単位を遷移とする自然数添字の順序合成である。
方針：既存の反復図式と余極限の余錐を、そのまま順序合成の構造へ渡す。
規約：Moss 2020 Corollary 30 の合成のデータ。
使われ方：anodyne 拡張の順序合成に関する閉性の適用。
-/
def exInfinityAnodyneSequence (X : SSet.{u}) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ (exInfinityUnit.app X) where
  F := exSequence.flip.obj X
  isoBot := Iso.refl _
  incl := (colimit.cocone (exSequence.flip.obj X)).ι
  isColimit := colimit.isColimit _
  map_mem n _ := by
    change SSet.anodyneExtensions ((exSequence.map (homOfLE (Nat.le_add_right n 1))).app X)
    simp only [exSequence, Functor.ofSequence_map_homOfLE_succ]
    exact exUnitAt_anodyne ((exIterate n).obj X)

/--
概要：Ex∞ への標準単位は anodyne 拡張である。
方針：各遷移が anodyne である順序合成に閉性を適用する。
規約：Moss 2020 Corollary 30。
使われ方：Ex∞ の単位の局所化での可逆性と置換の比較。
-/
@[kerodon 00ZH]
theorem exInfinityUnit_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (exInfinityUnit.app X) :=
  SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ _
    (exInfinityAnodyneSequence X).mem

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
