module

public import SerrePositivity.DifferentialGraded.Complexes.CompositionLaws
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
# 線形加法圏の複体の写像複体と合成

概要：層の加群圏にも使える写像複体と dg 合成を構成する。
方針：Mathlib の linearHomComplex と既存のテンソル複体の構成を再利用する。
規約：可換係数環と Hom の宇宙を合わせ、対象圏の宇宙は独立とする。
使われ方：KST D4・§13 決定11、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：任意の線形加法圏の複体間の写像複体。
方針：Mathlib の一般の linearHomComplex を使う。
規約：全次数の射の族を持ち、有界性は要求しない。
使われ方：KST D4、Toën §3.2 の層複体の dg 圏。
-/
abbrev mappingComplex (X Y : CochainComplex C ℤ) : Complex A :=
  CochainComplex.linearHomComplex A X Y

variable {A}

/--
概要：写像複体の通常順の合成の双次数成分。
方針：Mathlib の Cochain.comp の双線形性をテンソル積から持ち上げる。
規約：第一因子 g、第二因子 f を g∘f へ送る。
使われ方：KST D4、Toën §3.2 の dg 合成。
-/
def compositionComponent (X Y Z : CochainComplex C ℤ) (q p n : ℤ) (h : q + p = n) :
    (mappingComplex A Y Z).X q ⊗ (mappingComplex A X Y).X p ⟶
      (mappingComplex A X Z).X n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun g :=
        { toFun f := f.comp g (by omega)
          map_add' f f' := Cochain.add_comp f f' g _
          map_smul' a f := Cochain.smul_comp a f g _ }
      map_add' g g' := by apply LinearMap.ext; intro f; exact Cochain.comp_add f g g' (by omega)
      map_smul' a g := by apply LinearMap.ext; intro f; exact Cochain.comp_smul f a g (by omega) })

/--
概要：通常順の dg 合成は写像複体の射。
方針：δ_comp の Leibniz 則を既存 tensorLift に渡す。
規約：符号は先に書く g の次数に依存する。
使われ方：KST D4、Toën §3.2 の層複体の写像複体。
-/
def composition (X Y Z : CochainComplex C ℤ) :
    mappingComplex A Y Z ⊗ mappingComplex A X Y ⟶ mappingComplex A X Z :=
  tensorLift (compositionComponent X Y Z) (by
    intro q p
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro f
    change δ (q + p) (q + p + 1) (f.comp g (by omega)) =
      f.comp (δ q (q + 1) g) (by omega) +
      q.negOnePow • (δ p (p + 1) f).comp g (by omega)
    exact δ_comp f g (by omega) (p + 1) (q + 1) (q + p + 1) rfl rfl rfl)

/--
概要：豊穣順の合成は符号つき交換の後に通常順の合成を行う。
方針：既存のコチェインテンソルの対称性を再利用する。
規約：f ⊗ g の像は (-1)^(deg f deg g) g∘f。
使われ方：KST D4・§13 決定11、Toën §3.2 の dg 圏の規約。
-/
def forwardComposition (X Y Z : CochainComplex C ℤ) :
    mappingComplex A X Y ⊗ mappingComplex A Y Z ⟶ mappingComplex A X Z :=
  (SerrePositivity.cochainTensorSymmetry _ _).hom ≫ composition X Y Z

/--
概要：豊穣順の合成の純テンソル成分の計算。
方針：符号つき交換の既存成分公式と tensorLift の評価式を使う。
規約：対象圏が加群の圏であることは要求しない。
使われ方：KST D4、Toën §3.2 の単位と結合則の証明。
-/
lemma forwardComposition_component (X Y Z : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    ιTensorObj (mappingComplex A X Y) (mappingComplex A Y Z) p q n h ≫
      (forwardComposition X Y Z).f n =
    (p * q).negOnePow •
      ((β_ ((mappingComplex A X Y).X p) ((mappingComplex A Y Z).X q)).hom ≫
        compositionComponent X Y Z q p n (by omega)) := by
  dsimp only [forwardComposition, HomologicalComplex.comp_f]
  rw [← Category.assoc, SerrePositivity.ιTensorObj_cochainTensorSymmetry,
    Linear.units_smul_comp, Category.assoc]
  dsimp only [composition]
  rw [ι_tensorLift]

/--
概要：豊穣合成の純粋な斉次テンソル上の値。
方針：双次数成分の計算式を元に評価する。
規約：通常の Cochain.comp と Koszul 符号で表す。
使われ方：KST D4、Toën §3.2 の dg 合成の法則。
-/
lemma forwardComposition_apply (X Y Z : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) (f : Cochain X Y p) (g : Cochain Y Z q) :
    (forwardComposition X Y Z).f n
      (ιTensorObj (mappingComplex A X Y) (mappingComplex A Y Z) p q n h (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • f.comp g h := by
  have hc := forwardComposition_component (A := A) X Y Z p q n h
  have he := congr($(hc).hom (f ⊗ₜ[A] g))
  exact he

end SerrePositivity.KST.DerivedGeometry.LinearComplex
