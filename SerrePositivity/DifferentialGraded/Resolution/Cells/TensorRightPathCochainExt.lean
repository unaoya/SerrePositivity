module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare

/-! # 任意次数cellの全合成の微分整合性：TensorRightPathCochainExt

## 概要
任意次数cellの全合成の微分整合性：TensorRightPathCochainExt。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma tensorRightPathCochain_ext (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y ⊗ K) T p)
    (h : ∀ w : List I, (Cochain.ofHom (C.inclusion A D I w x y ▷ K)).comp f (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y ▷ K)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorRightCoproductIsColimit K (fun w : List I => C.term A D I w x y))).hom_ext
  rintro ⟨w⟩
  change (C.inclusion A D I w x y ▷ K).f i ≫ f.v i n hn =
    (C.inclusion A D I w x y ▷ K).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I w x y ⊗ K) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
