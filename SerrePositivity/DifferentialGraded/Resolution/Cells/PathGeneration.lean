module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrefixGeneration
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorBoundary

/-! # 元のHomと任意次数生成cellの反復合成によるpath生成式

## 概要
元のHomと任意次数生成cellの反復合成によるpath生成式。

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
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma prefixPath_generator (i : I) (x y : D) (p q b n : ℤ)
    (hb : C.degree i + q = b) (hn : p + b = n) (a : (homObject A D x (C.source i)).X p)
    (t : (C.internalHom A D I (C.target i) y).X q) :
    (C.prefixPath A D I i x y).f n
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) p b n hn (a ⊗ₜ[A]
          ιTensorObj (C.generator A D I i) (C.internalHom A D I (C.target i) y)
            (C.degree i) q b hb
            ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : C.Objects A D I)) (y := ⟨C.source i⟩) (z := ⟨y⟩)
      ((C.originalHomInclusion A D I x (C.source i)).f p a)
      (forward A (x := (⟨C.source i⟩ : C.Objects A D I)) (y := ⟨C.target i⟩) (z := ⟨y⟩)
        (C.generatorElement A D I i) t hb) hn := by
  have hp : (C.originalHom A D I x (C.source i) ▷ C.internalHom A D I (C.source i) y) ≫
      C.internalComposition A D I x (C.source i) y = C.internalPrepend A D I x (C.source i) y :=
    C.internalComposition_left_inclusion A D I [] x (C.source i) y
  have hg := C.prefixPath_generated A D I i x y
  rw [← hp] at hg
  have h := congrArg (fun f : homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) ⟶ C.internalHom A D I x y =>
    f.f n (ιTensorObj (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) p b n hn (a ⊗ₜ[A]
        ιTensorObj (C.generator A D I i) (C.internalHom A D I (C.target i) y)
          (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t)))) hg
  simp only [chain_comp_apply, whiskerLeft_apply, whiskerRight_apply] at h
  change _ = (C.attachedComposition A D I x (C.source i) y).f n
    (ιTensorObj (C.attachedHom A D I x (C.source i)) (C.attachedHom A D I (C.source i) y)
      p b n hn ((C.originalHomInclusion A D I x (C.source i)).f p a ⊗ₜ[A]
        (C.attachedComposition A D I (C.source i) (C.target i) y).f b
          (ιTensorObj (C.attachedHom A D I (C.source i) (C.target i))
            (C.attachedHom A D I (C.target i) y) (C.degree i) q b hb
            (C.generatorElement A D I i ⊗ₜ[A] t))))
  rw [attachedComposition_apply, attachedComposition_apply, originalHomInclusion_f]
  exact h.symm

lemma path_inclusion_generator (i : I) (w : List I) (x y : D) (p q b n : ℤ)
    (hb : C.degree i + q = b) (hn : p + b = n) (a : (homObject A D x (C.source i)).X p)
    (t : (C.term A D I w (C.target i) y).X q) :
    (C.inclusion A D I (i :: w) x y).f n
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn (a ⊗ₜ[A]
          ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
            (C.degree i) q b hb
            ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : C.Objects A D I)) (y := ⟨C.source i⟩) (z := ⟨y⟩)
      ((C.originalHomInclusion A D I x (C.source i)).f p a)
      (forward A (x := (⟨C.source i⟩ : C.Objects A D I)) (y := ⟨C.target i⟩) (z := ⟨y⟩)
        (C.generatorElement A D I i) ((C.inclusion A D I w (C.target i) y).f q t) hb) hn := by
  have h := congrArg (fun f : homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y) ⟶ C.internalHom A D I x y =>
    f.f n (ιTensorObj (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn (a ⊗ₜ[A]
        ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y) (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (C.prefixPath_inclusion A D I i x y w)
  simp only [chain_comp_apply, whiskerLeft_apply] at h
  exact h.symm.trans (C.prefixPath_generator A D I i x y p q b n hb hn a
    ((C.inclusion A D I w (C.target i) y).f q t))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
