module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Extension

/-! # cell付加からのdg関手を元の関手と指定原始元へ制限する

## 概要
cell付加からのdg関手を元の関手と指定原始元へ制限する。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I) {E : Type z} [DGCategory A E]

abbrev restrictFunctor (G : DGFunctor A (C.Objects A D I) E) : DGFunctor A D E :=
  (C.embedding A D I).comp G

def restrictPrimitives (G : DGFunctor A (C.Objects A D I) E) :
    PrimitiveData A D I C E (C.restrictFunctor A D I G) where
  primitive i := (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)
  boundary i := by
    have h := congrArg (fun f => f (C.generatorElement A D I i))
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).comm (C.degree i) (C.degree i + 1))
    change (homObject A E (G.obj ⟨C.source i⟩) (G.obj ⟨C.target i⟩)).d
      (C.degree i) (C.degree i + 1)
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)) =
      (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i + 1)
        ((C.attachedHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
          (C.generatorElement A D I i)) at h
    rw [differential_generatorElement] at h
    exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
