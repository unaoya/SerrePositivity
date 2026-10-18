module

public import SerrePositivity.KST.Comparison.GroupCompletionHomotopy
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.Algebra.Category.MonCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 単体的モノイドの台集合と単位基点の順序余極限

概要：単体的モノイドの台集合への忘却は順序余極限を保ち、単位基点を自然に付けられる。
方針：各次数での filtered colimit の保存と、射の単位保存を使う。
規約：KST Lemma 2.13 の安定 rank を実際の図式の余極限で扱う。
使われ方：安定 ĜL の Kan 性と K-L9 のホモトピー群の余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped Simplicial

/--
概要：単体的モノイドの台単体集合を取る忘却関手。
方針：モノイドの忘却で右から whiskering する。
規約：既存の monoidSpace と同じ対象・射を持つ。
使われ方：順序余極限の保存。
-/
def monoidSpaceFunctor : SimplicialObject MonCat.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ MonCat.{u} (Type u)).obj (forget MonCat)

/--
概要：単体的モノイドの台集合への忘却は自然数添字の余極限を保存する。
方針：モノイドの filtered colimit の保存を最小添字宇宙に制限し、図式圏で各次数に適用する。
規約：遷移射の単射性は不要。
使われ方：安定 ĜL の台集合を実際の余極限として扱う。
-/
instance monoidSpaceFunctor_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ monoidSpaceFunctor.{u} := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget MonCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  unfold monoidSpaceFunctor
  infer_instance

/--
概要：単体的モノイドを単位基点付きの単体集合へ送る関手。
方針：射の単位保存から点付き性を証明し、忘却射の恒等・合成を使う。
規約：基点は全次数の単位。
使われ方：安定 rank の図式に K-L9 のホモトピー群を施す。
-/
def monoidPointedFunctor : SimplicialObject MonCat.{u} ⥤ PointedSimplicialSet.{u} where
  obj := monoidPointed
  map {M N} f := Under.homMk (Functor.whiskerRight f (forget MonCat)) (by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro p
    exact map_one (f.app d).hom)
  map_id _ := by apply Under.UnderMorphism.ext; rfl
  map_comp _ _ := by apply Under.UnderMorphism.ext; rfl

/--
概要：単位基点を付けても台集合の Kan 性は変わらない。
方針：台集合の定義の一致を使う。
規約：元の単体的モノイドの Kan 性を入力とする。
使われ方：K-L9 の点付きホモトピー群の図式。
-/
instance monoidPointed_kanComplex (M : SimplicialObject MonCat.{u})
    [SSet.KanComplex (monoidSpace M)] : SSet.KanComplex (monoidPointed M).right :=
  inferInstanceAs (SSet.KanComplex (monoidSpace M))

/--
概要：単位基点付き対象の零次基点は元のモノイドの単位である。
方針：全次数の単位射を零次で評価する。
規約：厳密な基点の計算。
使われ方：有限 rank の係数表示の基点と点付き余極限の基点を合わせる。
-/
theorem monoidPointed_basepoint (M : SimplicialObject MonCat.{u}) :
    (monoidPointed M).basepoint = (1 : M.obj (op ⦋0⦌)) := rfl

end SerrePositivity.KST.Comparison
