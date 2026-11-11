module

public import SerrePositivity.KST.Spectra.TotalizationBoundaryLifting
public import SerrePositivity.KST.Spectra.CosimplicialRelativeWhitehead

/-!
概要：各段の π_* 同型である Reedy fibration の通常の Tot による保存。
方針：相対 matching の Whitehead と Tot の境界充填を合成する。
規約：両 Tot の Kan 性を明示し、点つき図式では各基点を参照頂点にする。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot の置換比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各段で全基点 π_* 同型な Reedy fibration は Kan な Tot でも全基点 π_* 同型。
方針：相対 matching の単射 RLP を次数帰納で得て Tot へ送る。
規約：各段の始域の参照頂点を明示する。
使われ方：Goerss–Jardine VIII §1。通常の Tot の相対 Whitehead。 -/
lemma CosimplicialTotalization.map_piIsomorphism_of_reedyFibration
    {X Y : CosimplicialObject SSet.{u}}
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    [KanComplex (CosimplicialTotalization.obj X)]
    [KanComplex (CosimplicialTotalization.obj Y)]
    (f : X ⟶ Y) (hf : reedyRight simplex SSet.modelCategoryQuillen.J.rlp f)
    (hπ : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j)) (e₀ : ∀ j, X.obj j _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (CosimplicialTotalization.map f) :=
  CosimplicialTotalization.map_piIsomorphism_of_matching_monoRight f
    (CosimplicialRelativeWhitehead.matching_rlp_of_levelwise f hf hπ e₀)

/-- 概要：点つき各段の π_* 同型である Reedy fibration は点つき Tot でも全基点 π_* 同型。
方針：基点を参照頂点にして基礎単体集合の相対 Whitehead を適用する。
規約：両 Tot の Kan 性を明示する。一般の係数の同型保存はまだ仮定しない。
使われ方：Goerss–Jardine VIII §1。点つき Tot の比較射。 -/
lemma PointedTotalization.map_piIsomorphism_of_reedyFibration
    {X Y : CosimplicialObject PointedSimplicialSet.{u}}
    [∀ j, KanComplex (X.obj j).right] [∀ j, KanComplex (Y.obj j).right]
    [KanComplex (PointedTotalization.obj X).right]
    [KanComplex (PointedTotalization.obj Y).right]
    (f : X ⟶ Y)
    (hf : reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (Functor.whiskerRight f PointedSimplicialSet.forget))
    (hπ : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedTotalization.map f).right := by
  let : ∀ j, KanComplex ((X ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (X.obj j).right)
  let : ∀ j, KanComplex ((Y ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (Y.obj j).right)
  let : KanComplex (CosimplicialTotalization.obj (X ⋙ PointedSimplicialSet.forget)) :=
    inferInstanceAs (KanComplex (PointedTotalization.obj X).right)
  let : KanComplex (CosimplicialTotalization.obj (Y ⋙ PointedSimplicialSet.forget)) :=
    inferInstanceAs (KanComplex (PointedTotalization.obj Y).right)
  exact CosimplicialTotalization.map_piIsomorphism_of_reedyFibration
    (Functor.whiskerRight f PointedSimplicialSet.forget) hf hπ
    (fun j ↦ PointedSimplicialSet.basepoint (X.obj j))

end

end SerrePositivity.KST.Spectra
