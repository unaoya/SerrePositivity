module

public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeNaturality

/-!
概要：通常の余錐を終対象を付加した関手として表示する。
方針：標準余錐と拡張関手の像から元の余錐を復元する。
規約：元の図式と頂点、指定変換の全ての成分を保持する。
使われ方：B5 の左 Kan の局所余錐の指定単位に沿う輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}

/-- 概要：通常の余錐を新しい終対象を付加した関手へ拡張する。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
def kanCoconeWithTerminalFunctor (c : Cocone F) : WithTerminal I ⥤ C :=
  WithTerminal.lift F c.ι.app (fun _i _j f ↦ c.w f)

/-- 概要：新しい終対象への包含の標準余錐。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
def kanWithTerminalCocone (I : Type u) [Category.{u} I] :
    Cocone (WithTerminal.incl : I ⥤ WithTerminal I) where
  pt := WithTerminal.star
  ι := { app := WithTerminal.homFrom
         naturality := fun _ _ _ ↦ rfl }

/-- 概要：拡張関手を標準余錐に適用すると元の余錐を回収する。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanCoconeWithTerminalFunctor_recover (c : Cocone F) :
    (kanCoconeWithTerminalFunctor c).mapCocone (kanWithTerminalCocone I) = c := by
  cases c
  congr 1

/-- 概要：nerve と点の join を終対象を付加した圏の nerve へ写す。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
def kanTerminalJoinNerveMap (I : Type u) [Category.{u} I] :
    join (nerve I) (Δ[0] : SSet.{u}) ⟶ nerve (WithTerminal I) :=
  (kanNerveCoconeEquiv (kanWithTerminalCocone I)).val

/-- 概要：native な余錐は終対象を付加した拡張関手の nerve で表示できる。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanNerveCocone_withTerminal (c : Cocone F) :
    kanTerminalJoinNerveMap I ≫ nerveMap (kanCoconeWithTerminalFunctor c) =
    (kanNerveCoconeEquiv c).val := by
  change (kanNerveCoconeEquiv (kanWithTerminalCocone I)).val ≫ _ = _
  rw [kanNerveCocone_mapCocone, kanCoconeWithTerminalFunctor_recover]
  rfl

end SerrePositivity.InfinityCategories.F1B
