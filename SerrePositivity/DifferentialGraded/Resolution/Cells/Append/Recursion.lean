module

public import SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin



/-!
# Resolution.Cells.Append.Recursion

## 概要
cell path の連結再帰・prefix・内部単位と cochain 外延性をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Differential（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Differential.lean） -/

/-! # 指定境界を持つ任意次数cell付加のHom微分

## 概要
内部微分に全境界置換作用素を加える。二乗零は具体的に証明済みの作用素の性質から得る。
合成のLeibnizと主dg圏instanceは後続で構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Differential
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def attachedHom (x y : D) : Complex A :=
  perturbComplex (C.internalHom A D I x y) (C.replacement A D I x y)
    (C.replacement_closed A D I x y) (C.replacement_square_zero A D I x y)

lemma attachedHom_X (x y : D) (n : ℤ) :
    (C.attachedHom A D I x y).X n = (C.internalHom A D I x y).X n := rfl

lemma attachedHom_d (x y : D) (n : ℤ) :
    (C.attachedHom A D I x y).d n (n + 1) =
    (C.internalHom A D I x y).d n (n + 1) + (C.replacement A D I x y).v n (n + 1) rfl :=
  perturbComplex_d _ _ _ _ _

/-- 元のHomの包含は追加微分後もchain mapとなる。 -/
def originalHomInclusion (x y : D) : homObject A D x y ⟶ C.attachedHom A D I x y :=
  CochainComplex.ofHom (fun n => (C.originalHom A D I x y).f n) (fun n => by
    have hz : (C.originalHom A D I x y).f n ≫ (C.replacement A D I x y).v n (n + 1) rfl = 0 := by
      simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
        congrArg (fun f : Cochain (homObject A D x y) (C.internalHom A D I x y) 1 =>
          f.v n (n + 1) rfl) (C.replacement_originalHom A D I x y)
    rw [attachedHom_d, comp_add, hz, add_zero]
    exact (C.originalHom A D I x y).comm n (n + 1))

lemma originalHomInclusion_f (x y : D) (n : ℤ) :
    (C.originalHomInclusion A D I x y).f n = (C.originalHom A D I x y).f n := rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Differential

/-! ## PathCochainDesc（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathCochainDesc.lean） -/

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
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathCochainDesc
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end PathCochainDesc

/-! ## InternalComposition（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalComposition.lean） -/

/-! # cell pathの連結を内部Hom直和へ延長した合成

## 概要
cell pathの連結を内部Hom直和へ延長した合成。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalComposition
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def internalComposition (x y z : D) :
    C.internalHom A D I x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  tensorCoproductDesc (fun w : List I => C.term A D I w x y)
    (fun v : List I => C.term A D I v y z) (C.internalHom A D I x z)
    (fun w v => C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z)

lemma internalComposition_inclusion (x y z : D) (w v : List I) :
    (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z) ≫ C.internalComposition A D I x y z =
      C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z :=
  tensorCoproductDesc_ι _ _ _ _ w v

lemma internalComposition_original_left (x y z : D) (w : List I) :
    (C.originalHom A D I x y ⊗ₘ C.inclusion A D I w y z) ≫ C.internalComposition A D I x y z =
      C.prependMap A D I w x y z ≫ C.inclusion A D I w x z :=
  C.internalComposition_inclusion A D I x y z [] w

lemma internalComposition_original_original (x y z : D) :
    (C.originalHom A D I x y ⊗ₘ C.originalHom A D I y z) ≫ C.internalComposition A D I x y z =
      eComp (Complex A) x y z ≫ C.originalHom A D I x z :=
  C.internalComposition_inclusion A D I x y z [] []

def appendRight (w : List I) (x y z : D) :
    C.term A D I w x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  tensorCoproductRightDesc (C.term A D I w x y) (fun v : List I => C.term A D I v y z)
    (C.internalHom A D I x z)
    (fun v => C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z)

lemma appendRight_inclusion (w v : List I) (x y z : D) :
    (C.term A D I w x y ◁ C.inclusion A D I v y z) ≫ C.appendRight A D I w x y z =
      C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z :=
  tensorCoproductRightDesc_ι _ _ _ _ v

lemma internalComposition_left_inclusion (w : List I) (x y z : D) :
    (C.inclusion A D I w x y ▷ C.internalHom A D I y z) ≫ C.internalComposition A D I x y z =
      C.appendRight A D I w x y z := tensorCoproductDesc_left _ _ _ _ w

abbrev internalPrepend (x y z : D) :
    homObject A D x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  C.appendRight A D I [] x y z

lemma internalPrepend_inclusion (x y z : D) (w : List I) :
    (homObject A D x y ◁ C.inclusion A D I w y z) ≫ C.internalPrepend A D I x y z =
      C.prependMap A D I w x y z ≫ C.inclusion A D I w x z :=
  C.appendRight_inclusion A D I [] w x y z

def internalIdentity (x : D) : 𝟙_ (Complex A) ⟶ C.internalHom A D I x x :=
  eId (Complex A) x ≫ C.originalHom A D I x x

lemma internalComposition_left_unit (x y : D) :
    (λ_ (C.internalHom A D I x y)).inv ≫
      C.internalIdentity A D I x ▷ C.internalHom A D I x y ≫
      C.internalComposition A D I x x y = 𝟙 _ := by
  apply C.internalHom_ext A D I x y
  intro w
  simp only [internalIdentity, comp_whiskerRight, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← tensorHom_def_assoc, internalComposition_original_left]
  rw [reassoc_of% (C.prependMap_left_unit A D I w x y)]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end InternalComposition

/-! ## Prefix（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Prefix.lean） -/

/-! # 先頭Homと任意次数生成元を全path直和に追加する包含

## 概要
先頭Homと任意次数生成元を全path直和に追加する包含。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Prefix
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def prefixCofanIsColimit (i : I) (x y : D) :
    IsColimit (Cofan.mk (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y))
      (fun w : List I => (homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))) :=
  isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft (C.generator A D I i) ⋙ tensorLeft (homObject A D x (C.source i)))
    (fun w : List I => C.term A D I w (C.target i) y)

def prefixPath (i : I) (x y : D) :
    homObject A D x (C.source i) ⊗ (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) ⟶
      C.internalHom A D I x y :=
  (C.prefixCofanIsColimit A D I i x y).desc
    (Cofan.mk (C.internalHom A D I x y) (fun w : List I => C.inclusion A D I (i :: w) x y))

lemma prefixPath_inclusion (i : I) (x y : D) (w : List I) :
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫
      C.prefixPath A D I i x y = C.inclusion A D I (i :: w) x y :=
  (C.prefixCofanIsColimit A D I i x y).fac
    (Cofan.mk (C.internalHom A D I x y) (fun w : List I => C.inclusion A D I (i :: w) x y)) ⟨w⟩

lemma prefixPathCochain_ext (i : I) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y)) T p)
    (h : ∀ w : List I,
      (Cochain.ofHom ((homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))).comp f (zero_add p) =
      (Cochain.ofHom ((homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))).comp g (zero_add p)) :
    f = g := by
  apply Cochain.ext
  intro a n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) a
  apply (isColimitOfPreserves ev (C.prefixCofanIsColimit A D I i x y)).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)).f a ≫ f.v a n hn =
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)).f a ≫ g.v a n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I (i :: w) x y) T p => z.v a n hn) (h w)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Prefix

/-! ## PrefixGeneration（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrefixGeneration.lean） -/

/-! # 元のHomと生成元の合成から前方path追加を復元する

## 概要
元のHomと生成元の合成から前方path追加を復元する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixGeneration
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma generator_internalComposition_inclusion (i : I) (w : List I) (y : D) :
    ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y) ≫
      (C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y =
    (C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
      C.appendMap A D I [i] w (C.source i) (C.target i) y ≫
        C.inclusion A D I (i :: w) (C.source i) y := by
  rw [generatorInclusion, comp_whiskerRight, Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, internalComposition_inclusion]
  rfl

lemma prefixPath_generated (i : I) (x y : D) :
    (homObject A D x (C.source i)) ◁
      ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y) ≫
      C.internalPrepend A D I x (C.source i) y = C.prefixPath A D I i x y := by
  apply (C.prefixCofanIsColimit A D I i x y).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫
      (homObject A D x (C.source i)) ◁
        ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
          C.internalComposition A D I (C.source i) (C.target i) y) ≫
        C.internalPrepend A D I x (C.source i) y =
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫ C.prefixPath A D I i x y
  rw [prefixPath_inclusion, ← whiskerLeft_comp_assoc, generator_internalComposition_inclusion]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [internalPrepend_inclusion]
  have h := congrArg (fun f => f ≫ C.inclusion A D I (i :: w) x y)
    (C.prependMap_generatorTerm_append A D I i w x y)
  simpa only [term_cons, whiskerLeft_comp, Category.assoc, Category.id_comp] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PrefixGeneration

/-! ## AppendRecursion（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendRecursion.lean） -/

/-! # 左pathの先頭生成元を残す連結の再帰式

## 概要
左pathの先頭生成元を残す連結の再帰式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendRecursion
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_cons (b : I) (w : List I) (x y z : D) :
    C.appendRight A D I (b :: w) x y z =
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) ≫
          C.prefixPath A D I b x z := by
  apply (tensorLeftCoproductIsColimit (C.term A D I (b :: w) x y)
    (fun v : List I => C.term A D I v y z)).hom_ext
  rintro ⟨v⟩
  have hm : ((C.generator A D I b ⊗ C.term A D I w (C.target b) y) ◁
      C.inclusion A D I v y z) ≫
      (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z =
    (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z ≫
        (C.generator A D I b) ◁ C.inclusion A D I (w ++ v) (C.target b) z := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, appendRight_inclusion,
      whiskerLeft_comp]
  have ht : ((homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)) ◁ C.inclusion A D I v y z) ≫
      (α_ (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
          (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) =
    (α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.inclusion A D I (w ++ v) (C.target b) z) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, hm]
    simp only [whiskerLeft_comp]
  have h := congrArg (fun f => f ≫ C.prefixPath A D I b x z) ht
  simp only [Category.assoc, prefixPath_inclusion] at h
  change (C.term A D I (b :: w) x y ◁ C.inclusion A D I v y z) ≫
    C.appendRight A D I (b :: w) x y z = _
  rw [appendRight_inclusion]
  simpa only [Cofan.mk_ι_app, term, appendMap, inclusion, List.cons_append,
    whiskerLeft_comp, Category.assoc] using h.symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendRecursion

/-! ## AppendPrepend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendPrepend.lean） -/

/-! # 任意次数cell path：AppendPrepend

## 概要
任意次数cell path：AppendPrepend。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendPrepend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 元のHomを先頭へ作用させる操作と有限path連結は結合する。 -/
@[reassoc] lemma appendMap_prepend (w v : List I) (x y z t : D) :
    (C.prependMap A D I w x y z ▷ C.term A D I v z t) ≫ C.appendMap A D I w v x z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.term A D I v z t)).hom ≫
      (homObject A D x y) ◁ C.appendMap A D I w v y z t ≫ C.prependMap A D I (w ++ v) x y t := by
  cases w with
  | nil => exact C.prependMap_assoc A D I v x y z t
  | cons b w =>
    simpa only [prependMap, appendMap, term, tensorHom_id, List.cons_append] using
      tensorJoin_right_action (homObject A D x y) (homObject A D y (C.source b))
        (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) z)
        (C.term A D I v z t) (C.generator A D I b ⊗ C.term A D I (w ++ v) (C.target b) t)
        (eComp (Complex A) x y (C.source b))
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) z) (C.term A D I v z t)).hom ≫
          (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) z t)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendPrepend

/-! ## AppendRightPrepend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendRightPrepend.lean） -/

/-! # 任意次数cell path：AppendRightPrepend

## 概要
任意次数cell path：AppendRightPrepend。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendRightPrepend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_prepend (w : List I) (x y z t : D) :
    (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t ≫ C.internalPrepend A D I x y t := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y ⊗ C.term A D I w y z)
    (fun v : List I => C.term A D I v z t)).hom_ext
  rintro ⟨v⟩
  change ((homObject A D x y ⊗ C.term A D I w y z) ◁ C.inclusion A D I v z t) ≫
      (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t =
    ((homObject A D x y ⊗ C.term A D I w y z) ◁ C.inclusion A D I v z t) ≫
      (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t ≫ C.internalPrepend A D I x y t
  rw [whisker_exchange_assoc, appendRight_inclusion, appendMap_prepend_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, appendRight_inclusion,
    whiskerLeft_comp_assoc, internalPrepend_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendRightPrepend

/-! ## InternalUnits（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalUnits.lean） -/

/-! # cell pathの全直和上の合成の右単位

## 概要
cell pathの全直和上の合成の右単位。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalUnits
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_right_unit (w : List I) (x y : D) :
    (ρ_ (C.term A D I w x y)).inv ≫ C.term A D I w x y ◁ C.internalIdentity A D I y ≫
      C.appendRight A D I w x y y = C.inclusion A D I w x y := by
  induction w generalizing x with
  | nil =>
    change (ρ_ (homObject A D x y)).inv ≫
      homObject A D x y ◁ C.internalIdentity A D I y ≫ C.internalPrepend A D I x y y = _
    simp only [internalIdentity, originalHom, whiskerLeft_comp, Category.assoc]
    rw [internalPrepend_inclusion]
    simpa only [prependMap, originalHom] using
      e_comp_id_assoc (Complex A) x y (C.originalHom A D I x y)
  | cons b w ih =>
    have h := tensorCarry_right_unit (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y y)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y) (C.internalIdentity A D I y)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y y)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y y)
    have ht := tensorCarry_right_unit (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y y) (C.internalHom A D I (C.target b) y) (C.internalIdentity A D I y)
      (C.appendRight A D I w (C.target b) y y)
    rw [ih (C.target b)] at ht
    rw [ht] at h
    have hp := congrArg (fun f => f ≫ C.prefixPath A D I b x y) h
    simp only [Category.assoc, prefixPath_inclusion] at hp
    simpa only [appendRight_cons, term, Category.assoc] using hp

lemma internalComposition_right_unit (x y : D) :
    (ρ_ (C.internalHom A D I x y)).inv ≫
      C.internalHom A D I x y ◁ C.internalIdentity A D I y ≫
      C.internalComposition A D I x y y = 𝟙 _ := by
  apply C.internalHom_ext A D I x y
  intro w
  simp only [Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    internalComposition_left_inclusion, appendRight_right_unit]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end InternalUnits

/-! ## CompositionPrefix（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionPrefix.lean） -/

/-! # 任意次数cell path：CompositionPrefix

## 概要
任意次数cell path：CompositionPrefix。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionPrefix
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma composition_prefix_left_ι (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
    C.internalHom A D I y z) ≫ (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫
      C.internalComposition A D I x y z = C.appendRight A D I (b :: w) x y z := by
  rw [← comp_whiskerRight_assoc, prefixPath_inclusion, internalComposition_left_inclusion]

lemma composition_prefix_middle_ι (b : I) (w : List I) (y z : D) :
    (((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y) ▷ C.internalHom A D I y z) ≫
    (α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z =
  (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
    (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_inclusion]

lemma composition_prefix_outer_ι (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
    C.internalHom A D I y z) ≫
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) =
  (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
    (C.internalHom A D I y z)).hom ≫
  (homObject A D x (C.source b)) ◁
    ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, composition_prefix_middle_ι]

/-- 各path上で先頭追加と全合成の二つの順序を比較する。 -/
lemma composition_prefix_restrict (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
      C.internalHom A D I y z) ≫ (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫
      C.internalComposition A D I x y z =
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
      C.internalHom A D I y z) ≫
      (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
        (C.internalHom A D I y z)).hom ≫ (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y
          z)).hom ≫
          (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) ≫ C.prefixPath A D I
            b x z := by
  have hr := congrArg (fun f => f ≫ C.prefixPath A D I b x z)
    (C.composition_prefix_outer_ι A D I b w x y z)
  simp only [Category.assoc] at hr
  exact (C.composition_prefix_left_ι A D I b w x y z).trans
      ((C.appendRight_cons A D I b w x y z).trans hr.symm)

/-- 先頭Homと生成元を追加してから合成しても、後方を合成してから追加しても一致する。 -/
lemma internalComposition_prefixPath (b : I) (x y z : D) :
    (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫ C.internalComposition A D I x y z =
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) ≫ C.prefixPath A D I b
          x z := by
  apply tensorLeftTwoRightCoproduct_hom_ext (homObject A D x (C.source b)) (C.generator A D I b)
    (C.internalHom A D I y z) (fun w : List I => C.term A D I w (C.target b) y)
  intro w
  exact C.composition_prefix_restrict A D I b w x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionPrefix

/-! ## CompositionPrepend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionPrepend.lean） -/

/-! # 任意次数cell path：CompositionPrepend

## 概要
任意次数cell path：CompositionPrepend。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionPrepend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma internalComposition_prepend (x y z t : D) :
    (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫ C.internalComposition A D I x z t =
    (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t ≫ C.internalPrepend A D I x y t := by
  apply tensorLeftRightCoproduct_hom_ext (homObject A D x y) (C.internalHom A D I z t)
    (fun w : List I => C.term A D I w y z)
  intro w
  let s : (homObject A D x y ⊗ C.term A D I w y z) ⊗ C.internalHom A D I z t ⟶
      (homObject A D x y ⊗ C.internalHom A D I y z) ⊗ C.internalHom A D I z t :=
    ((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t
  change s ≫ (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    s ≫ (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t ≫ C.internalPrepend A D I x y t
  have hl : (((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t) ≫
      (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t := by
    rw [← comp_whiskerRight_assoc, internalPrepend_inclusion, comp_whiskerRight,
      Category.assoc, internalComposition_left_inclusion]
  have hm : (((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t) ≫
      (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t := by
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_inclusion]
  have hr := congrArg (fun f => f ≫ C.internalPrepend A D I x y t) hm
  simpa only [Category.assoc] using hl.trans ((C.appendRight_prepend A D I w x y z t).trans hr.symm)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionPrepend

/-! ## PrependBoundaryRows（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrependBoundaryRows.lean） -/

/-! # 任意次数cell path：PrependBoundaryRows

## 概要
任意次数cell path：PrependBoundaryRows。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrependBoundaryRows
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)
/-- 一つの境界置換項を全直和へ入れた後も先頭Hom作用と可換する。 -/
lemma prependMap_replaceSummand (w : List I) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (C.replaceSummand A D I w i x z) (zero_add 1)
      =
    ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
      (C.internalHom A D I y z)).f 1 (C.replaceSummand A D I w i y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  rw [replaceSummand, replaceSummand, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_replaceFace, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, internalPrepend_inclusion]

/-- 一つのpath上の有限消去和は先頭Hom作用と可換する。 -/
lemma prependMap_replaceRow (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (C.replaceRow A D I w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
      (C.internalHom A D I y z)).f 1 (C.replaceRow A D I w y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  let L : Cochain (C.term A D I w x z) (C.internalHom A D I x z) 1 →+
      Cochain (homObject A D x y ⊗ C.term A D I w y z) (C.internalHom A D I x z) 1 :=
    { toFun := fun f => (Cochain.ofHom (C.prependMap A D I w x y z)).comp f (zero_add 1)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  let R : Cochain (C.term A D I w y z) (C.internalHom A D I y z) 1 →+
      Cochain (homObject A D x y ⊗ C.term A D I w y z) (C.internalHom A D I x z) 1 :=
    { toFun := fun f => ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
        (C.internalHom A D I y z)).f 1 f).comp
        (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1)
      map_zero' := by rw [map_zero]; exact Cochain.zero_comp _ _
      map_add' := fun f g => by rw [map_add, Cochain.add_comp] }
  change L (C.replaceRow A D I w x z) = R (C.replaceRow A D I w y z)
  rw [replaceRow, replaceRow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact C.prependMap_replaceSummand A D I w i x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PrependBoundaryRows

/-! ## TensorPathCochainExt（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/TensorPathCochainExt.lean） -/

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
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorPathCochainExt
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorPathCochainExt

/-! ## TensorRightPathCochainExt（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/TensorRightPathCochainExt.lean） -/

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
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorRightPathCochainExt
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorRightPathCochainExt

/-! ## TensorTwoPathCochainExt（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/TensorTwoPathCochainExt.lean） -/

/-! # 二つの全path直和のtensorからの任意次数cochainの判定

## 概要
二つの全path直和のtensorからの任意次数cochainの判定。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorTwoPathCochainExt
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma tensorTwoPathCochain_ext (x y z : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y ⊗ C.internalHom A D I y z) T p)
    (h : ∀ w v : List I,
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp f
      (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp g (zero_add p)) :
    f = g := by
  apply C.tensorRightPathCochain_ext A D I x y (C.internalHom A D I y z) p
  intro w
  apply C.tensorLeftPathCochain_ext A D I y z (C.term A D I w x y) p
  intro v
  simpa only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    ← tensorHom_def'] using h w v

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end TensorTwoPathCochainExt
