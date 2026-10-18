module

public import SerrePositivity.KST.Spectra.CosimplicialKanReplacement
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：余単体 horn fibration の合成・積射影と終射の表示の独立性。
方針：次数帰納の弱因子分解系で右類を RLP と同定し、その閉性を使う。
規約：モデル圏構造を仮定しない通常の持ち上げ性の計算。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の一般の係数同型の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.CosimplicialHornFibration

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：余単体 horn の右類は相対 latching anodyne の RLP。
方針：通常の弱因子分解系を Reedy 次数帰納で移す。
規約：HT-KQ や Reedy モデル圏のインスタンスは不要。
使われ方：Goerss–Jardine VII §4。右類の閉性の入力。 -/
lemma right_eq_rlp : reedyRight simplex SSet.modelCategoryQuillen.J.{u}.rlp =
    (reedyLeft simplex SSet.anodyneExtensions.{u}).rlp := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  let := weakFactorizationSystem simplex SSet.anodyneExtensions.{u}
    SSet.modelCategoryQuillen.J.{u}.rlp
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)
  exact (MorphismProperty.rlp_eq_of_wfs
    (reedyLeft simplex SSet.anodyneExtensions.{u})
    (reedyRight simplex SSet.modelCategoryQuillen.J.{u}.rlp)).symm

/-- 概要：Reedy horn fibration は合成で閉じる。
方針：RLP 類の合成閉性に帰着する。
規約：各相対 matching の充填を別々に合成する仮定は不要。
使われ方：Goerss–Jardine VII §4。因子分解の二つの射影。 -/
lemma comp {X Y Z : CosimplicialObject SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : reedyRight simplex SSet.modelCategoryQuillen.J.rlp f)
    (hg : reedyRight simplex SSet.modelCategoryQuillen.J.rlp g) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp (f ≫ g) := by
  rw [right_eq_rlp] at hf hg ⊢
  exact (reedyLeft simplex SSet.anodyneExtensions.{u}).rlp.comp_mem _ _ hf hg

/-- 概要：Kan な余単体対象との積からの第一射影は Reedy horn fibration。
方針：第二因子の終射の引き戻しとして積の正方形を見る。
規約：終射は関手圏で選択された終対象への射。
使われ方：Goerss–Jardine VII §4。係数の写像の二射影への分解。 -/
lemma prod_fst (X Y : CosimplicialObject SSet.{u})
    (hY : reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from Y)) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp (prod.fst : X ⨯ Y ⟶ X) := by
  rw [right_eq_rlp] at hY ⊢
  exact (reedyLeft simplex SSet.anodyneExtensions.{u}).rlp.of_isPullback
    (IsPullback.of_hasBinaryProduct' X Y).flip hY

/-- 概要：Kan な余単体対象との積からの第二射影は Reedy horn fibration。
方針：第一因子の終射の引き戻しとして積を見る。
規約：第二因子自体の Kan 性は不要。
使われ方：Goerss–Jardine VII §4。係数の写像の二射影への分解。 -/
lemma prod_snd (X Y : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from X)) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [right_eq_rlp] at hX ⊢
  exact (reedyLeft simplex SSet.anodyneExtensions.{u}).rlp.of_isPullback
    (IsPullback.of_hasBinaryProduct' X Y) hX

/-- 概要：選択された終対象と各段一定の終対象は同じ Reedy Kan 条件を与える。
方針：二つの終対象の一意な同型で arrow を比較する。
規約：射そのものの同型から右類を移す。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の具体的な終図式との接続。 -/
lemma terminal_iff (X : CosimplicialObject SSet.{u}) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from X) ↔
      reedyRight simplex SSet.modelCategoryQuillen.J.rlp
        (CosimplicialKanReplacement.terminalArrows.obj X).hom := by
  let t := Functor.isTerminalConst SimplexCategory (terminalIsTerminal (C := SSet.{u}))
  let e := t.uniqueUpToIso (terminalIsTerminal (C := CosimplicialObject SSet.{u}))
  let a : Arrow.mk (CosimplicialKanReplacement.terminalArrows.obj X).hom ≅
      Arrow.mk (terminal.from X) := Arrow.isoMk (Iso.refl _) e (by
        exact (Category.id_comp _).trans (terminal.hom_ext _ _))
  rw [right_eq_rlp]
  exact ((reedyLeft simplex SSet.anodyneExtensions.{u}).rlp.arrow_iso_iff a).symm

end

end SerrePositivity.KST.Spectra.CosimplicialHornFibration
