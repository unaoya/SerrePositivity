module

public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import Mathlib.Logic.Small.List
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin


public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-!
# Quotient.Path.Construction

## 概要
有限 path の構成・連結と ε 消去 cochainをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Paths（旧 SerrePositivity/DifferentialGraded/Quotient/Paths.lean） -/

/-! # 明示的dg商の有限pathとtensor項

中間対象は指定full部分圏Sに属する。各中間対象に次数−1の記号を一つ置く。
ここでの複体は各tensor項の内部微分のみを持つ。dε=idによる長さを下げる項は後続で追加する。
-/

@[expose] public section Paths
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- pathの収縮記号を置く中間対象の有限語。空語も許す。 -/
abbrev Word {D : Type v} (S : Set D) := List S

/-- 各中間対象に対応する収縮記号の合計次数。 -/
def epsilonDegree {D : Type v} {S : Set D} (w : Word S) : ℤ := -(w.length : ℤ)

@[simp] lemma epsilonDegree_nil {D : Type v} (S : Set D) :
    epsilonDegree ([] : Word S) = 0 := rfl

@[simp] lemma epsilonDegree_cons {D : Type v} {S : Set D} (b : S) (w : Word S) :
    epsilonDegree (b :: w) = epsilonDegree w - 1 := by
  simp [epsilonDegree]
  omega

lemma epsilonDegree_append {D : Type v} {S : Set D} (w z : Word S) :
    epsilonDegree (w ++ z) = epsilonDegree w + epsilonDegree z := by
  dsimp [epsilonDegree]
  rw [List.length_append, Nat.cast_add]
  abel

/-- 収縮記号を表す次数−1のA複体。内部微分は零である。 -/
abbrev epsilonComplex : Complex A := complexSphere A (-1)

/-- path x→b₁→…→bᵣ→yの全次数tensor項。元のHomの次数を制限しない。 -/
def term {S : Set D} : Word S → D → D → Complex A
  | [], x, y => homObject A D x y
  | b :: w, x, y => homObject A D x b.val ⊗ (epsilonComplex A ⊗ term w b.val y)

@[simp] lemma term_nil (S : Set D) (x y : D) :
    term A D ([] : Word S) x y = homObject A D x y := rfl

@[simp] lemma term_cons {S : Set D} (b : S) (w : Word S) (x y : D) :
    term A D (b :: w) x y = homObject A D x b.val ⊗
      (epsilonComplex A ⊗ term A D w b.val y) := rfl

/-- 単一の収縮記号を持つpath項への、実際の次数−1生成射。 -/
def epsilonTerm {S : Set D} (b : S) : epsilonComplex A ⟶ term A D [b] b.val b.val :=
  (λ_ (epsilonComplex A)).inv ≫
    (eId (Complex A) b.val ⊗ₘ
      ((ρ_ (epsilonComplex A)).inv ≫ (𝟙 (epsilonComplex A) ⊗ₘ eId (Complex A) b.val)))

variable [Small.{u} D]

instance wordSmall (S : Set D) : Small.{u} (Word S) := inferInstanceAs (Small.{u} (List S))

/-- 全有限path項の直和。ここでは内部微分だけを持つ補助複体。 -/
abbrev internalHom (S : Set D) (x y : D) : Complex A := ∐ (fun w : Word S => term A D w x y)

/-- 指定path項から全path直和への包含。 -/
def ι (S : Set D) (x y : D) (w : Word S) : term A D w x y ⟶ internalHom A D S x y :=
  Sigma.ι (fun w : Word S => term A D w x y) w

/-- 空pathの包含。後続の最終微分でも元のdg Homの包含となる。 -/
def originalHom (S : Set D) (x y : D) : homObject A D x y ⟶ internalHom A D S x y :=
  ι A D S x y []

/-- 指定対象bの次数−1記号を全path直和へ入れる。まだ収縮の方程式は主張しない。 -/
def epsilon (S : Set D) (b : S) : epsilonComplex A ⟶ internalHom A D S b.val b.val :=
  epsilonTerm A D b ≫ ι A D S b.val b.val [b]

/-- path直和からの射は各有限path項上で決まる。 -/
lemma hom_ext (S : Set D) (x y : D) {T : Complex A} (f g : internalHom A D S x y ⟶ T)
    (h : ∀ w : Word S, ι A D S x y w ≫ f = ι A D S x y w ≫ g) : f = g :=
  Sigma.hom_ext f g h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Paths

/-! ## PathUniversal（旧 SerrePositivity/DifferentialGraded/Quotient/PathUniversal.lean） -/

/-! # 内部微分を持つpath直和の普遍性と空部分圏の比較

最終dg商の収縮方程式を課す前の、直和の普遍性だけを記録する。
-/

@[expose] public section PathUniversal
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全path項に与えたchain map族を内部微分の直和から延長する。 -/
def desc (S : Set D) (x y : D) {T : Complex A} (f : ∀ w : Word S, term A D w x y ⟶ T) :
    internalHom A D S x y ⟶ T := Sigma.desc f

@[reassoc (attr := simp)]
lemma ι_desc (S : Set D) (x y : D) {T : Complex A}
    (f : ∀ w : Word S, term A D w x y ⟶ T) (w : Word S) :
    ι A D S x y w ≫ desc A D S x y f = f w := Sigma.ι_comp_desc f w

/-- 内部微分のpath直和からの射は、全path項のchain map族と同値。 -/
def homEquiv (S : Set D) (x y : D) (T : Complex A) :
    (internalHom A D S x y ⟶ T) ≃ (∀ w : Word S, term A D w x y ⟶ T) where
  toFun f w := ι A D S x y w ≫ f
  invFun := desc A D S x y
  left_inv f := by apply hom_ext A D S x y; intro w; simp
  right_inv f := by funext w; exact ι_desc A D S x y f w

/-- 空部分圏を通る中間対象はないので、有限語は必ず空。 -/
lemma word_empty {D : Type v} (w : Word (∅ : Set D)) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w => exact False.elim b.property

/-- 空部分圏の場合、path直和は元のHom複体そのものである。 -/
def emptyHomIso (x y : D) : homObject A D x y ≅ internalHom A D ∅ x y where
  hom := originalHom A D ∅ x y
  inv := desc A D ∅ x y (fun w => eqToHom (by rw [word_empty w]; rfl))
  hom_inv_id := by simp [originalHom, ι, desc]
  inv_hom_id := by
    apply hom_ext A D ∅ x y
    intro w
    have hw := word_empty w
    subst w
    simp [originalHom, ι, desc]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathUniversal

/-! ## PathPrefix（旧 SerrePositivity/DifferentialGraded/Quotient/PathPrefix.lean） -/

/-! # 先頭Homとεを保持する全path直和への包含 -/

@[expose] public section PathPrefix
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 前方Homとεをtensorしたpath cofanも余積である。 -/
def prefixPathCofanIsColimit {S : Set D} (b : S) (x y : D) :
    IsColimit (Cofan.mk (homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y))
      (fun w : Word S => (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))) :=
  isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft (epsilonComplex A) ⋙ tensorLeft (homObject A D x b.val))
    (fun w : Word S => term A D w b.val y)

/-- 前方Homとεを追加し、全path直和へ入れる内部chain map。 -/
def prefixPath {S : Set D} (b : S) (x y : D) :
    homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y) ⟶
      internalHom A D S x y :=
  (prefixPathCofanIsColimit A D b x y).desc
    (Cofan.mk (internalHom A D S x y) (fun w : Word S => ι A D S x y (b :: w)))

lemma prefixPath_ι {S : Set D} (b : S) (x y : D) (w : Word S) :
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫
      prefixPath A D b x y = ι A D S x y (b :: w) :=
  (prefixPathCofanIsColimit A D b x y).fac
    (Cofan.mk (internalHom A D S x y) (fun w : Word S => ι A D S x y (b :: w))) ⟨w⟩

/-- 前方Homとεをtensorした直和のcochainも各pathへの制限で決まる。 -/
lemma prefixPathCochain_ext {S : Set D} (b : S) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain
      (homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y)) T p)
    (h : ∀ w : Word S,
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
          f (zero_add p) =
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
          g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev (prefixPathCofanIsColimit A D b x y)).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)).f i ≫
      f.v i n hn =
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D (b :: w) x y) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathPrefix

/-! ## PathCochainExt（旧 SerrePositivity/DifferentialGraded/Quotient/PathCochainExt.lean） -/

/-! # 全path直和を始域とする任意次数cochainの包含による判定 -/

@[expose] public section PathCochainExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉性を仮定せず、全path直和のcochainを各pathへの制限で判定する。 -/
lemma pathCochain_ext (S : Set D) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (ι A D S x y w)).comp f (zero_add p) =
      (Cochain.ofHom (ι A D S x y w)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (colimit.isColimit (Discrete.functor (fun w : Word S => term A D w x y)))).hom_ext
  intro w
  change (ι A D S x y w.as).f i ≫ f.v i n hn =
    (ι A D S x y w.as).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D w.as x y) T p => z.v i n hn) (h w.as)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathCochainExt

/-! ## PathCochainDesc（旧 SerrePositivity/DifferentialGraded/Quotient/PathCochainDesc.lean） -/

/-! # 任意次数のpath cochainの全直和への貼合せ -/

@[expose] public section PathCochainDesc
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉性を仮定せず、各pathの任意次数cochainを全直和からのcochainへ貼り合わせる。 -/
def pathCochainDesc (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p) :
    Cochain (internalHom A D S x y) T p :=
  Cochain.mk (fun i n hn =>
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : Word S => term A D w x y)).desc
        (Cofan.mk (T.X n) (fun w => (f w).v i n hn)))

lemma pathCochainDesc_precomp (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (pathCochainDesc A D S x y T p f) (zero_add p) = f w := by
  apply Cochain.ext
  intro i n hn
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, pathCochainDesc, Cochain.mk_v]
  exact (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (fun w : Word S => term A D w x y)).fac
      (Cofan.mk (T.X n) (fun w => (f w).v i n hn)) ⟨w⟩

lemma pathCochainDesc_unique (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p)
    (g : Cochain (internalHom A D S x y) T p)
    (hg : ∀ w, (Cochain.ofHom (ι A D S x y w)).comp g (zero_add p) = f w) :
    g = pathCochainDesc A D S x y T p f := by
  apply pathCochain_ext A D S x y p
  intro w
  rw [hg, pathCochainDesc_precomp]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathCochainDesc

/-! ## PathComposition（旧 SerrePositivity/DifferentialGraded/Quotient/PathComposition.lean） -/

/-! # 有限path tensor項の連結

内部微分に関するchain mapを構成する。最終dg商のε消去微分との両立や結合則は後続で検証する。
Homの合成には主モデルの豊穣合成を使い、εを含むtensor因子の順序を保つ。
-/

@[expose] public section PathComposition
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元のHomをpathの先頭Homと豊穣合成する。 -/
def prependMap {S : Set D} : ∀ (w : Word S) (x y z : D),
    homObject A D x y ⊗ term A D w y z ⟶ term A D w x z
  | [], x, y, z => eComp (Complex A) x y z
  | b :: w, x, y, z =>
    (α_ (homObject A D x y) (homObject A D y b.val)
      (epsilonComplex A ⊗ term A D w b.val z)).inv ≫
      (eComp (Complex A) x y b.val ⊗ₘ 𝟙 (epsilonComplex A ⊗ term A D w b.val z))

@[simp] lemma prependMap_nil (S : Set D) (x y z : D) :
    prependMap A D ([] : Word S) x y z = eComp (Complex A) x y z := rfl

/-- 二つのpathの連結。境界に隣接するHomだけを豊穣合成する。 -/
def appendMap {S : Set D} : ∀ (w z : Word S) (x y t : D),
    term A D w x y ⊗ term A D z y t ⟶ term A D (w ++ z) x t
  | [], z, x, y, t => prependMap A D z x y t
  | b :: w, z, x, y, t =>
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (term A D z y t)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (term A D w b.val y) (term A D z y t)).hom ≫
        (epsilonComplex A) ◁ appendMap w z b.val y t)

@[simp] lemma appendMap_nil_left {S : Set D} (w : Word S) (x y z : D) :
    appendMap A D [] w x y z = prependMap A D w x y z := rfl

@[simp] lemma appendMap_nil_nil (S : Set D) (x y z : D) :
    appendMap A D ([] : Word S) [] x y z = eComp (Complex A) x y z := rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathComposition

/-! ## PrependUnit（旧 SerrePositivity/DifferentialGraded/Quotient/PrependUnit.lean） -/

/-! # 有限pathの先頭Hom合成の左単位則 -/

@[expose] public section PrependUnit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

@[reassoc] lemma prependMap_left_unit {S : Set D} (w : Word S) (x y : D) :
    (λ_ (term A D w x y)).inv ≫ eId (Complex A) x ▷ term A D w x y ≫
      prependMap A D w x x y = 𝟙 (term A D w x y) := by
  cases w with
  | nil => exact e_id_comp (Complex A) x y
  | cons b w =>
    simpa only [prependMap, term_cons, tensorHom_id] using
      tensorJoin_left_unit (homObject A D x x) (homObject A D x b.val)
        (epsilonComplex A ⊗ term A D w b.val y) (eId (Complex A) x)
        (eComp (Complex A) x x b.val) (e_id_comp (Complex A) x b.val)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependUnit

/-! ## PrependAssociativity（旧 SerrePositivity/DifferentialGraded/Quotient/PrependAssociativity.lean） -/

/-! # 有限pathの先頭Hom合成の結合則 -/

@[expose] public section PrependAssociativity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の二つのHomを先に合成しても、pathへ順に合成しても一致する。 -/
lemma prependMap_assoc {S : Set D} (w : Word S) (x y z t : D) :
    (eComp (Complex A) x y z ▷ term A D w z t) ≫ prependMap A D w x z t =
    (α_ (homObject A D x y) (homObject A D y z) (term A D w z t)).hom ≫
      (homObject A D x y) ◁ prependMap A D w y z t ≫ prependMap A D w x y t := by
  cases w with
  | nil => exact (e_assoc' (Complex A) x y z t).symm
  | cons b w =>
    simpa only [prependMap, term_cons, tensorHom_id] using
      tensorJoin_assoc (homObject A D x y) (homObject A D y z) (homObject A D z b.val)
        (homObject A D x z) (homObject A D y b.val) (homObject A D x b.val)
        (epsilonComplex A ⊗ term A D w b.val t)
        (eComp (Complex A) x y z) (eComp (Complex A) y z b.val)
        (eComp (Complex A) x z b.val) (eComp (Complex A) x y b.val)
        (e_assoc' (Complex A) x y z b.val).symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependAssociativity

/-! ## EpsilonAppend（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonAppend.lean） -/

/-! # 単一ε pathを連結したときの単位因子の消去 -/

@[expose] public section EpsilonAppend
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma epsilonTerm_append {S : Set D} (b : S) (w : Word S) (y : D) :
    (epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y =
    (λ_ (epsilonComplex A ⊗ term A D w b.val y)).inv ≫
      eId (Complex A) b.val ▷ (epsilonComplex A ⊗ term A D w b.val y) := by
  simpa only [epsilonTerm, appendMap, List.nil_append, term_nil] using
    tensorSandwich_append (epsilonComplex A) (homObject A D b.val b.val) (term A D w b.val y)
      (eId (Complex A) b.val) (prependMap A D w b.val b.val y)
      (prependMap_left_unit A D w b.val y)

lemma prependMap_epsilonTerm_append {S : Set D} (b : S) (w : Word S) (x y : D) :
    (homObject A D x b.val) ◁
      ((epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y) ≫
      prependMap A D (b :: w) x b.val y = 𝟙 (term A D (b :: w) x y) := by
  rw [epsilonTerm_append]
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_right_unit (homObject A D x b.val) (homObject A D b.val b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (eId (Complex A) b.val)
      (eComp (Complex A) x b.val b.val) (e_comp_id (Complex A) x b.val)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonAppend

/-! ## EpsilonCochainExt（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonCochainExt.lean） -/

/-! # 標準ε生成元上の評価による次数0 cochainの判定 -/

@[expose] public section EpsilonCochainExt
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma epsilon_generator_span (e : (epsilonComplex A).X (-1)) :
    e = ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom e) •
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  calc
    e = (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom e) := by
      change e = ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv) e
      rw [Iso.hom_inv_id]
      rfl
    _ = _ := by rw [← map_smul]; simp only [smul_eq_mul, mul_one]

lemma epsilonMiddleCochain_ext₀ {K P T : Complex A}
    (f g : Cochain (K ⊗ (epsilonComplex A ⊗ P)) T 0)
    (h : ∀ (i j n : ℤ) (hn : i + ((-1) + j) = n) (x : K.X i) (y : P.X j),
      f.v n n (add_zero n) (ιTensorObj K (epsilonComplex A ⊗ P) i ((-1) + j) n hn
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
      g.v n n (add_zero n) (ιTensorObj K (epsilonComplex A ⊗ P) i ((-1) + j) n hn
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y)))) :
    f = g := by
  apply rightTripleCochain_ext₀
  intro i k j n hn x e y
  by_cases hk : k = -1
  · subst k
    rw [epsilon_generator_span A e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j n hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonCochainExt

/-! ## EpsilonDifferential（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonDifferential.lean） -/

/-! # 収縮記号を消す次数+1 cochain

ε複体の次数−1生成元を単位複体の次数0生成元へ送る。
これは内部Hom微分について閉じた次数+1 cochainであり、閉零chain mapではない。
-/

@[expose] public section EpsilonDifferential
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- dε=idに使う、εを単位へ送る次数+1の線形cochain。 -/
def eraseEpsilon : Cochain (epsilonComplex A) (𝟙_ (Complex A)) 1 :=
  Cochain.fromSingleMk (p := -1) (q := 0) (n := 1)
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (by omega)

/-- ε消去cochainは内部Hom微分について閉じている。 -/
lemma eraseEpsilon_closed : δ 1 2 (eraseEpsilon A) = 0 := by
  rw [eraseEpsilon, Cochain.δ_fromSingleMk _ _ 2 1 (by omega)]
  change Cochain.fromSingleMk
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv ≫
      ((single (ModuleCat.{u} A) (.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} A))).d 0 1)
    (show (-1 : ℤ) + 2 = 1 by omega) = 0
  simp only [single_obj_d, comp_zero, Cochain.fromSingleMk_zero]

/-- 唯一の非零成分は次数−1から0へ単位Aをそのまま送る。 -/
lemma eraseEpsilon_v :
    (eraseEpsilon A).v (-1) 0 (by omega) =
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv :=
  Cochain.fromSingleMk_v _ _

/-- 次数−1の標準生成元の像は次数0の標準生成元。 -/
lemma eraseEpsilon_generator :
    (eraseEpsilon A).v (-1) 0 (by omega)
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) := by
  rw [eraseEpsilon_v]
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv
    (((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonDifferential

/-! ## EpsilonTensor（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonTensor.lean） -/

/-! # ε消去cochainのtensorによる拡張

左の因子を通る際のKoszul符号は主Homのtensor写像で与える。
-/

@[expose] public section EpsilonTensor
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左に任意非有界複体を置いたε消去。 -/
def eraseLeftTensor (P : Complex A) : Cochain (P ⊗ epsilonComplex A) (P ⊗ 𝟙_ (Complex A)) 1 :=
  (tensorLeftHom P (epsilonComplex A) (𝟙_ (Complex A))).f 1 (eraseEpsilon A)

lemma eraseLeftTensor_closed (P : Complex A) : δ 1 2 (eraseLeftTensor A P) = 0 :=
  homComplexMap_closed (tensorLeftHom P (epsilonComplex A) (𝟙_ (Complex A)))
    1 (eraseEpsilon A) (eraseEpsilon_closed A)

/-- 右に任意非有界複体を置いたε消去。 -/
def eraseRightTensor (P : Complex A) : Cochain (epsilonComplex A ⊗ P) (𝟙_ (Complex A) ⊗ P) 1 :=
  (tensorRightHom P (epsilonComplex A) (𝟙_ (Complex A))).f 1 (eraseEpsilon A)

lemma eraseRightTensor_closed (P : Complex A) : δ 1 2 (eraseRightTensor A P) = 0 :=
  homComplexMap_closed (tensorRightHom P (epsilonComplex A) (𝟙_ (Complex A)))
    1 (eraseEpsilon A) (eraseEpsilon_closed A)

/-- 左因子の次数iを通るε消去には(-1)^iが付く。 -/
lemma eraseLeftTensor_apply (P : Complex A) (i a n : ℤ)
    (ha : i + (-1) = a) (hn : a + 1 = n) (x : P.X i) (e : (epsilonComplex A).X (-1)) :
    (eraseLeftTensor A P).v a n hn
      (ιTensorObj P (epsilonComplex A) i (-1) a ha (x ⊗ₜ[A] e)) =
    i.negOnePow • ιTensorObj P (𝟙_ (Complex A)) i 0 n (by omega)
      (x ⊗ₜ[A] (eraseEpsilon A).v (-1) 0 (by omega) e) := by
  simpa only [eraseLeftTensor, one_mul] using
    (tensorLeftHom_apply_of_sum P (epsilonComplex A) (𝟙_ (Complex A)) 1 i (-1) a 0 n
      ha (by omega) hn
      (eraseEpsilon A) x e)

/-- 右因子を置く場合は追加の符号を持たない。 -/
lemma eraseRightTensor_apply (P : Complex A) (j a n : ℤ)
    (ha : (-1) + j = a) (hn : a + 1 = n) (e : (epsilonComplex A).X (-1)) (x : P.X j) :
    (eraseRightTensor A P).v a n hn
      (ιTensorObj (epsilonComplex A) P (-1) j a ha (e ⊗ₜ[A] x)) =
    ιTensorObj (𝟙_ (Complex A)) P 0 j n (by omega)
      ((eraseEpsilon A).v (-1) 0 (by omega) e ⊗ₜ[A] x) := by
  exact tensorRightHom_apply P (epsilonComplex A) (𝟙_ (Complex A))
    1 (-1) j a n ha hn (eraseEpsilon A) e x

/-- P⊗(ε⊗Q)からP⊗Qへの次数+1の消去。 -/
def eraseMiddle (P Q : Complex A) : Cochain (P ⊗ (epsilonComplex A ⊗ Q)) (P ⊗ Q) 1 :=
  ((tensorLeftHom P (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
    (eraseRightTensor A Q)).comp (Cochain.ofHom (P ◁ (λ_ Q).hom)) (add_zero 1)

/-- 中間のε消去は内部微分と反交換する。 -/
lemma eraseMiddle_closed (P Q : Complex A) : δ 1 2 (eraseMiddle A P Q) = 0 := by
  rw [eraseMiddle, δ_comp_ofHom]
  have h : δ 1 2
      ((tensorLeftHom P (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
        (eraseRightTensor A Q)) = 0 :=
    homComplexMap_closed _ 1 _ (eraseRightTensor_closed A Q)
  rw [h]
  exact Cochain.zero_comp _ _

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonTensor

/-! ## EpsilonHomogeneousExt（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonHomogeneousExt.lean） -/

/-! 任意次数の cochain を標準 ε 生成元上で判定する。 -/

@[expose] public section EpsilonHomogeneousExt
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

lemma epsilonMiddleCochain_ext {K P T : Complex R} {d : ℤ}
    (f g : Cochain (K ⊗ (epsilonComplex R ⊗ P)) T d)
    (h : ∀ (i j a n : ℤ) (ha : i + ((-1) + j) = a) (hn : a + d = n)
      (x : K.X i) (y : P.X j),
      f.v a n hn (ιTensorObj K (epsilonComplex R ⊗ P) i ((-1) + j) a ha
        (x ⊗ₜ[R] ιTensorObj (epsilonComplex R) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] y))) =
      g.v a n hn (ιTensorObj K (epsilonComplex R ⊗ P) i ((-1) + j) a ha
        (x ⊗ₜ[R] ιTensorObj (epsilonComplex R) P (-1) j ((-1) + j) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] y)))) :
    f = g := by
  apply rightTripleCochain_ext
  intro i k j a n ha hn x e y
  by_cases hk : k = -1
  · subst k
    rw [epsilon_generator_span R e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j a n ha hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonHomogeneousExt
