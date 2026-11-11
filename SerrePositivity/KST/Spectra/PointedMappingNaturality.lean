module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality

public import SerrePositivity.KST.Spectra.SuspensionLoop

/-!
概要：点つき写像空間の源の制限と smash の随伴の整合性。
方針：等化子への包含後に curry と smash の商の自然性を計算する。
規約：既存 Spectra の通常の smash・内部 Hom の基礎だけを借りる。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの厳密射との比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：内部 Hom の点として表した射の源を制限すると通常の合成になる。
方針：閉構造の pre との一致と右単位子の自然性を使う。
規約：curry' による通常の射の表示。
使われ方：BF 1978 §2。写像空間の零次単体とスペクトルの射の照合。 -/
theorem curry'_pre {X Y Z : PointedSimplicialSet.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) :
    MonoidalClosed.curry' f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z = MonoidalClosed.curry' (i ≫ f) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, MonoidalClosed.curry', MonoidalClosed.curry_pre_app,
    MonoidalClosed.curry']
  congr 1
  rw [← Category.assoc, rightUnitor_naturality, Category.assoc]

end

end SerrePositivity.KST.Spectra.PointedMapping
