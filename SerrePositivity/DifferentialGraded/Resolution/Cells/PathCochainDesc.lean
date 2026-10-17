module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare

/-! # 任意次数のpath cochainの全直和への貼合せ

## 概要
任意次数のpath cochainの全直和への貼合せ。

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
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 閉性を仮定せず、各pathの任意次数cochainを全直和からのcochainへ貼り合わせる。 -/
def pathCochainDesc (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : List I, Cochain (C.term A D I w x y) T p) :
    Cochain (C.internalHom A D I x y) T p :=
  Cochain.mk (fun i n hn =>
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : List I => C.term A D I w x y)).desc
        (Cofan.mk (T.X n) (fun w => (f w).v i n hn)))

lemma pathCochainDesc_precomp (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : List I, Cochain (C.term A D I w x y) T p) (w : List I) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      (C.pathCochainDesc A D I x y T p f) (zero_add p) = f w := by
  apply Cochain.ext
  intro i n hn
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, pathCochainDesc, Cochain.mk_v]
  exact (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (fun w : List I => C.term A D I w x y)).fac
      (Cofan.mk (T.X n) (fun w => (f w).v i n hn)) ⟨w⟩

lemma pathCochainDesc_unique (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : List I, Cochain (C.term A D I w x y) T p)
    (g : Cochain (C.internalHom A D I x y) T p)
    (hg : ∀ w, (Cochain.ofHom (C.inclusion A D I w x y)).comp g (zero_add p) = f w) :
    g = C.pathCochainDesc A D I x y T p f := by
  apply C.pathCochain_ext A D I x y p
  intro w
  rw [hg, pathCochainDesc_precomp]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
