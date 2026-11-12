module

public import SerrePositivity.KST.Comparison.GroupCompletionBasepoint
public import SerrePositivity.KST.Comparison.GrouplikeComparison
public import SerrePositivity.KST.Comparison.LocalizedHomotopyComparison
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.LoopZeroHomotopy

/-!
# 群状モノイドの分類空間のホモトピー類

概要：標準群完備化比較を K-L9 の実際のホモトピー類とループの次数移動へ渡す。
方針：標準写像を元のモノイドの Kan 置換へ延長し、その局所化同型から全単射を得る。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13。入力の Kan 性を要求しない。
使われ方：安定 ĜL の分類空間の具体的な π_n の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：単位を基点とする単体的モノイドの台集合。
方針：全次数の単位射を Under の対象にする。
規約：単体的群構造は要求しない。
使われ方：点付き Kan 置換への入力。
-/
def monoidPointed (M : SimplicialObject MonCat.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (monoidUnitMap M)

/--
概要：標準群完備化写像を元のモノイドの Kan 置換へ延長できる。
方針：置換単位の anodyne 性とループ空間の Kan 性を使う。
規約：延長は標準写像に厳密に一致する。
使われ方：Kan 複体間の比較への接続。
-/
theorem exists_groupCompletionKanExtension (M : SimplicialObject MonCat.{u}) :
    ∃ f : (Spectra.PointedKanReplacement.obj (monoidPointed M)).right ⟶
        (monoidGroupCompletionSpace M).right,
      AnodyneKanReplacement.unit.app (monoidSpace M) ≫ f = monoidGroupCompletionMap M :=
  KanHomotopyExtension.exists_extension _ (AnodyneKanReplacement.unit_anodyne _)
    ((fibration_iff _).1 (inferInstance : Fibration
      (terminal.from (monoidGroupCompletionSpace M).right))) (monoidGroupCompletionMap M)

/--
概要：標準群完備化写像の点付き Kan 延長。
方針：anodyne 延長を選び、元の写像と置換単位の基点保存から点付き性を得る。
規約：追加の比較の同値性は定義に含めない。
使われ方：K-L9 の全基点ホモトピー不変性の適用。
-/
def groupCompletionKanMap (M : SimplicialObject MonCat.{u}) :
    Spectra.PointedKanReplacement.obj (monoidPointed M) ⟶ monoidGroupCompletionSpace M :=
  Under.homMk (Classical.choose (exists_groupCompletionKanExtension M)) (by
    change (monoidUnitMap M ≫ AnodyneKanReplacement.unit.app (monoidSpace M)) ≫ _ = _
    rw [Category.assoc, Classical.choose_spec (exists_groupCompletionKanExtension M)]
    exact monoidGroupCompletionMap_unit M)

/--
概要：Kan 延長は置換単位との合成で元の標準群完備化写像へ戻る。
方針：選んだ延長の分解式を使う。
規約：標準写像を別の比較射に置き換えない。
使われ方：局所化での二対三性。
-/
theorem groupCompletionKanMap_fac (M : SimplicialObject MonCat.{u}) :
    AnodyneKanReplacement.unit.app (monoidSpace M) ≫ (groupCompletionKanMap M).right =
      monoidGroupCompletionMap M :=
  Classical.choose_spec (exists_groupCompletionKanExtension M)

/--
概要：群状モノイドの標準写像の Kan 延長は局所化可逆である。
方針：置換単位と元の標準写像の局所化可逆性を分解式から打ち消す。
規約：Segal 1974 Proposition 1.5 の既証明の比較を使う。
使われ方：全ホモトピー類の同値の構成。
-/
theorem groupCompletionKanMap_localized_isIso (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (groupCompletionKanMap M).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  let i := AnodyneKanReplacement.unit.app (monoidSpace M)
  have : IsIso (Q.map i) := Localization.inverts Q anodyneExtensions i
    (AnodyneKanReplacement.unit_anodyne _)
  have hc : Q.map i ≫ Q.map (groupCompletionKanMap M).right =
      Q.map (monoidGroupCompletionMap M) :=
    (Q.map_comp _ _).symm.trans (congrArg Q.map (groupCompletionKanMap_fac M))
  have : IsIso (Q.map i ≫ Q.map (groupCompletionKanMap M).right) :=
    hc.symm ▸ monoidGroupCompletionMap_localized_isIso M hM
  exact (isIso_comp_left_iff (Q.map i) _).1 this

/--
概要：点付き局所化同型は K-L9 の基点付きホモトピー類の同値を誘導する。
方針：全基点の同値の後に、基点保存の等式による恒等同型の移送を合成する。
規約：零次数を含む。π_n の定義は K-L9 から借りる。
使われ方：ループの次数移動との合成。
-/
def pointedKanHomotopyEquivOfLocalizedIso {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X.right n X.basepoint ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y.right n Y.basepoint :=
  (kanHomotopyEquivOfLocalizedIso f.right hf X.basepoint n).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n (Iso.refl Y.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f))

/--
概要：群状モノイドの Kan 模型の π_n は分類空間の π_(n+1) と同値。
方針：標準群完備化写像の Kan 延長の比較と K-L9 の loop の次数移動を合成する。
規約：KST Lemma 2.13 の delooping 部分。n=0 も含む集合の同値。
使われ方：基本群と行列の高次ホモトピー類の具体的な計算。
-/
def monoidBarHomotopyEquiv (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (Spectra.PointedKanReplacement.obj (monoidPointed M)).right n
        (Spectra.PointedKanReplacement.obj (monoidPointed M)).basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (monoidBarKanPointed M).right (n + 1)
        (monoidBarKanPointed M).basepoint :=
  (pointedKanHomotopyEquivOfLocalizedIso (groupCompletionKanMap M)
    (groupCompletionKanMap_localized_isIso M hM) n).trans
      (Spectra.loopHomotopyEquiv (monoidBarKanPointed M) n)

end SerrePositivity.KST.Comparison
