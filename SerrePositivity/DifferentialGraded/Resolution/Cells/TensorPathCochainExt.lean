module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 任意次数cell path：TensorPathCochainExt

## 概要
任意次数cell path：TensorPathCochainExt。

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

/-- 左tensorしたpath直和の任意次数cochainも各pathへの制限で判定できる。 -/
lemma tensorLeftPathCochain_ext (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (K ⊗ C.internalHom A D I x y) T p)
    (h : ∀ w : List I, (Cochain.ofHom (K ◁ C.inclusion A D I w x y)).comp f (zero_add p) =
      (Cochain.ofHom (K ◁ C.inclusion A D I w x y)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorLeftCoproductIsColimit K (fun w : List I => C.term A D I w x y))).hom_ext
  rintro ⟨w⟩
  change (K ◁ C.inclusion A D I w x y).f i ≫ f.v i n hn =
    (K ◁ C.inclusion A D I w x y).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (K ⊗ C.term A D I w x y) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
