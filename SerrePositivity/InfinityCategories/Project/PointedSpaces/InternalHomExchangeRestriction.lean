module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：二つの源を同時に制限する射は内部 Hom の交換と可換。
方針：各源の制限の自然性を制限と後合成の可換式で貼る。
規約：通常の閉 braided モノイダル圏で扱う。
使われ方：Goerss–Jardine I §7、HA §1.4.2。二つの Kan 円の制限と交換の整合性。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 概要：二つの源の射による反復内部 Hom の同時の制限。
方針：外側の源を制限してから内側の源の制限を後合成する。
規約：制限の二つの射は任意。
使われ方：HA §1.4.2。Kan 置換を二つの loop 変数に同時に適用する。 -/
def restrictBoth {A' A K' K : C} (i : A' ⟶ A) (j : K' ⟶ K) (Y : C) :
    (ihom A).obj ((ihom K).obj Y) ⟶ (ihom A').obj ((ihom K').obj Y) :=
  (MonoidalClosed.pre i).app ((ihom K).obj Y) ≫
    (ihom A').map ((MonoidalClosed.pre j).app Y)

/-- 概要：二つの源の同時の制限は内部 Hom の交換と可換。
方針：内側の制限の自然性、外側の制限の自然性、pre の標的の自然性を順に使う。
規約：交換後は制限の二つの射の順序も交換する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。通常の円と Kan 円の交換の比較。 -/
theorem restrictBoth_exchange {A' A K' K : C} (i : A' ⟶ A) (j : K' ⟶ K) (Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth j i Y =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth i j Y ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A' K' Y).hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left]
  rw [← Category.assoc, (MonoidalClosed.pre i).naturality ((MonoidalClosed.pre j).app Y),
    Category.assoc]

omit [BraidedCategory C] in
/-- 概要：二つの源の同時の制限は標的の写像について自然。
方針：pre の自然変換を左右に whisker した合成の自然性を使う。
規約：二つの内部 Hom の後合成を比較する。
使われ方：HA §1.4.2。円の Kan 置換と標的の loop の符号反転の可換性。 -/
theorem restrictBoth_post {A' A K' K Y Z : C} (i : A' ⟶ A) (j : K' ⟶ K) (f : Y ⟶ Z) :
    (ihom A).map ((ihom K).map f) ≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth i j Z =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth i j Y ≫ (ihom A').map ((ihom K').map f) :=
  (Functor.whiskerLeft (ihom K) (MonoidalClosed.pre i) ≫
    Functor.whiskerRight (MonoidalClosed.pre j) (ihom A')).naturality f

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
