module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityKan
public import SerrePositivity.KST.Comparison.ExInfinityHomotopyPullback
public import SerrePositivity.KST.Comparison.KanReplacementSquares

/-!
# 図式の Ex∞ 置換と四角形

概要：図式を成分ごとに Ex∞ で置換し、単位の自然性と四角形の性質の不変性をまとめる。
方針：Ex∞ の単位とその自然性を図式の各成分に適用する。
規約：Segal 1974 Lemma 1.7 の Kan な基底への還元。
使われ方：中央の基底が任意の場合を Kan の場合へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Functor
open SerrePositivity.SimplicialModel
variable {D : Type v} [Category.{w} D]

/--
概要：図式から成分ごとの Ex∞ 置換への単位。
方針：各対象の単位を、元の図式の射に対する自然性でまとめる。
規約：始域は元の図式そのもの。
使われ方：元の span と Kan な span の比較。
-/
def diagramExInfinityUnit (F : D ⥤ SSet.{u}) : F ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity where
  app d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (F.obj d)
  naturality {_ _} f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (F.map f)

/--
概要：図式の Ex∞ 単位は図式の自然変換と可換である。
方針：各成分に Ex∞ の単位の自然性を適用する。
規約：置換した自然変換は whiskerRight で与える。
使われ方：span の射の可換な比較。
-/
theorem diagramExInfinityUnit_naturality {F G : D ⥤ SSet.{u}} (α : F ⟶ G) :
    α ≫ diagramExInfinityUnit G = diagramExInfinityUnit F ≫ whiskerRight α _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity := by
  apply NatTrans.ext
  funext d
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (α.app d)

/--
概要：図式の Ex∞ 単位は各成分で局所化同型である。
方針：Ex∞ の単位の既証の anodyne 性からの可逆性を使う。
規約：図式の対象や射の Kan 性は不要。
使われ方：円筒の比較の成分ごとの可逆性。
-/
theorem diagramExInfinityUnit_localized_isIso (F : D ⥤ SSet.{u}) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((diagramExInfinityUnit F).app d)) :=
  inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (F.obj d))))

/--
概要：図式の Ex∞ 置換は各添字の射に沿う四角形のホモトピー引き戻し性を保つ。
方針：四角形を Ex∞ へ送ったときの保存・反映を使う。
規約：自然性の等式の証明の選択は性質に影響しない。
使われ方：Kan な基底への貼り合わせの仮定の移送。
-/
theorem diagramExInfinity_arrowSquare_iff {F G : D ⥤ SSet.{u}} (α : F ⟶ G)
    {d e : D} (θ : d ⟶ e) :
    IsHomotopyPullback (naturalitySquare (diagramArrow θ) (whiskerRight α _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity)) ↔
      IsHomotopyPullback (naturalitySquare (diagramArrow θ) α) :=
  isHomotopyPullback_exInfinity_iff (naturalitySquare (diagramArrow θ) α)

end SerrePositivity.KST.Comparison
