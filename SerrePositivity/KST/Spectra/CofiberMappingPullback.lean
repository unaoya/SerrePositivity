module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.CofiberMappingPullback

public import SerrePositivity.KST.Spectra.PointedCofiber
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：点つき cofiber からの写像空間を与える引き戻し。
方針：内部 Hom の源に関する反変関手が極限を保つことを使う。
規約：通常の単体集合の厳密な pullback の主張。
使われ方：Goerss–Jardine I §7、HTT A.3.3。loop と path fiber の比較。
-/

@[expose] public section

universe v w u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cofiber からの点つき写像空間は構造制限の pullback。
方針：点つき pushout の反対に極限を保つ Hom 関手を適用する。
規約：Kan 性はこの圏論的な同定には不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path fiber の表示。 -/
theorem cofiberMapping_isPullback {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection i) Z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.fromPoint (pointedCofiber i)) Z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.toPoint X) Z) := by
  have h := ((pointedCofiber_isPushout i).op.flip).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map] using h

/-- 概要：点からの点つき Hom の基礎単体集合は終対象。
方針：点が初対象であることを極限保存の反変 Hom 関手で移す。
規約：点は smash の単位でなく零対象。
使われ方：Goerss–Jardine I §7。cofiber の Hom の pullback を基点 fiber に移す。 -/
def homPointIsTerminal (Z : PointedSimplicialSet.{u}) :
    IsTerminal (PointedObject.basedHom PointedObject.point Z).right :=
  IsTerminal.isTerminalObj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Z) _ PointedObject.point_isZero.isInitial.op

end

end SerrePositivity.KST.Spectra
