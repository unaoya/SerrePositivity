module

public import SerrePositivity.KST.Spectra.CosimplicialHornFibration
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：余単体 Reedy Kan 置換の終射の条件と各段の π_* 同型保存。
方針：終図式への因子分解の右射と単位の自然性を使う。
規約：射の比較には元の各段の Kan 性と始域の参照頂点を明示する。
使われ方：Goerss–Jardine VII §4、VIII §1。任意の Kan 図式の置換した Tot の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialKanReplacement

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Reedy 置換の選択された終対象への射は相対 matching horn RLP。
方針：因子分解の右射と一意な終図式への射を同定する。
規約：関手圏で選択された終対象を使う表示。
使われ方：Goerss–Jardine VII §4。Tot の Reedy 条件との接続。 -/
lemma terminal_rlp (X : CosimplicialObject SSet.{u}) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from (functor.obj X)) := by
  apply (CosimplicialHornFibration.terminal_iff _).mpr
  have he : (terminalArrows.obj (functor.obj X)).hom =
      CosimplicialHornFactorization.factorization.p.app (terminalArrows.obj X) := by
    apply NatTrans.ext
    funext j
    exact terminal.hom_ext _ _
  rw [he]
  exact reedy_terminal_rlp X

/-- 概要：各段の π_* 同型は Reedy Kan 置換した図式の各段でも π_* 同型。
方針：自然な単位の両側の同型性と元の射の同型性から前側を消去する。
規約：始域の各段の頂点を明示する。
使われ方：Goerss–Jardine VII §4、VIII §1。置換した Tot の係数のホモトピー不変性。 -/
lemma map_piIsomorphism {X Y : CosimplicialObject SSet.{u}}
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    (f : X ⟶ Y) (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j))
    (e₀ : ∀ j, X.obj j _⦋0⦌) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (functor.obj X).obj j) (Y := (functor.obj Y).obj j)
      ((functor.map f).app j) := by
  have hn := congr_app (unit.naturality f) j
  change f.app j ≫ (unit.app Y).app j =
    (unit.app X).app j ≫ (functor.map f).app j at hn
  have hc := (hf j).comp (unit_piIsomorphism Y j)
  rw [hn] at hc
  exact (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (unit_piIsomorphism X j)) hc (e₀ j)

end

end SerrePositivity.KST.Spectra.CosimplicialKanReplacement
