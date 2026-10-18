module

public import SerrePositivity.KST.Spectra.CosimplicialTotalization
public import SerrePositivity.KST.Spectra.PointedCosimplicialKanFunctor

/-!
概要：点つき余単体図式の通常の Tot と Reedy 置換後の Kan 性。
方針：各基点の一定な族を標準単体の重み付き end へ送り、Reedy horn 充填を使う。
規約：任意の図式の Tot と、置換後に Kan になる Tot を区別する。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。L9e の点つき Tot の段ごとの構成。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：余単体 Reedy 置換の通常の Tot は Kan 複体。
方針：終図式への因子分解の右射を一意な終射と同定して Reedy 充填へ渡す。
規約：元の余単体図式の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。通常の Tot の Kan 置換模型。 -/
lemma CosimplicialTotalization.kanComplex_replacement (X : CosimplicialObject SSet.{u}) :
    KanComplex (CosimplicialTotalization.obj (CosimplicialKanReplacement.functor.obj X)) := by
  apply CosimplicialTotalization.kanComplex
  have he : (CosimplicialKanReplacement.terminalArrows.obj
      (CosimplicialKanReplacement.functor.obj X)).hom =
      CosimplicialHornFactorization.factorization.p.app
        (CosimplicialKanReplacement.terminalArrows.obj X) := by
    apply NatTrans.ext
    funext j
    exact terminal.hom_ext _ _
  rw [he]
  exact CosimplicialKanReplacement.reedy_terminal_rlp X

namespace PointedTotalization

/-- 概要：点つき図式の基点を標準単体の変数について一定の族にする。
方針：標準単体からパラメーターへの第二射影に基点を後合成する。
規約：パラメーターは単体集合のモノイダル単位。
使われ方：Goerss–Jardine VIII §1。通常の Tot の基点。 -/
def basepointFamily (X : CosimplicialObject PointedSimplicialSet.{u}) :
    SimplexTensorBoundary.diagram (𝟙_ SSet.{u}) ⟶ (X ⋙ PointedSimplicialSet.forget) where
  app j := snd (SSet.stdSimplex.obj j) (𝟙_ SSet.{u}) ≫ (X.obj j).hom
  naturality i j g := by
    change (SSet.stdSimplex.map g ▷ _) ≫ (snd _ _ ≫ (X.obj j).hom) =
      (snd _ _ ≫ (X.obj i).hom) ≫ (X.map g).right
    rw [← Category.assoc, whiskerRight_snd, Category.assoc, Under.w]

/-- 概要：点つき余単体図式の通常の Tot。
方針：基礎単体集合の Tot に基点の一定な族を選ぶ。
規約：ここでは Reedy 条件も Kan 性も仮定しない。
使われ方：Goerss–Jardine VIII §1。点つき Tot の実際の対象。 -/
def obj (X : CosimplicialObject PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (CosimplicialTotalization.lift (basepointFamily X))

/-- 概要：Reedy 条件を満たす点つき図式の通常の Tot は Kan。
方針：基礎単体集合の Tot の horn 充填を使う。
規約：Reedy 条件は基点を忘却した図式に課す。
使われ方：Goerss–Jardine VIII §1。点つき Tot の Kan 性。 -/
lemma kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (CosimplicialKanReplacement.terminalArrows.obj (X ⋙ PointedSimplicialSet.forget)).hom) :
    KanComplex (obj X).right :=
  CosimplicialTotalization.kanComplex (X ⋙ PointedSimplicialSet.forget) hX

/-- 概要：点つき Reedy 置換を施した図式の通常の Tot。
方針：基点を保存する関手的 Reedy 置換へ Tot を適用する。
規約：値は点つき Kan 複体であることを別に証明する。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。任意の余単体係数の通常の Tot の模型。 -/
def replacementObj (X : CosimplicialObject PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u} :=
  obj (PointedCosimplicialKanReplacement.obj X)

/-- 概要：Reedy 置換後の点つき Tot の基礎単体集合は Kan。
方針：忘却した置換の Tot の Kan 性を適用する。
規約：元の図式の各値の Kan 性も不要。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。Tot の段ごとの Kan 複体。 -/
instance replacementObj_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u}) :
    KanComplex (replacementObj X).right := by
  change KanComplex (CosimplicialTotalization.obj
    (CosimplicialKanReplacement.functor.obj (X ⋙ PointedSimplicialSet.forget)))
  exact CosimplicialTotalization.kanComplex_replacement (X ⋙ PointedSimplicialSet.forget)

end PointedTotalization

end

end SerrePositivity.KST.Spectra
