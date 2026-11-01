module

public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import Mathlib.Logic.Small.List
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorTwoUnitInsertion
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinActionNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Resolution.Cells.Boundary

## 概要
17 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Paths（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Paths.lean） -/

/-! # 任意次数・異なる端点を持つdg生成cellのpath項

## 概要
既存Homを間に置き、新生成元を任意整数次数のsphereで表す。
ここでの微分は内部微分のみ。指定境界による追加微分は後続で構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Paths
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)

/-- 生成元はsource→targetの次数degreeの射で、微分は指定cycle。 -/
structure Family where
  source : I → D
  target : I → D
  degree : I → ℤ
  boundary : ∀ i, complexCycles A (homObject A D (source i) (target i)) (degree i + 1)

namespace Family
variable (C : Family A D I)

abbrev generator (i : I) : Complex A := complexSphere A (C.degree i)

/-- 空語には既存Homを置く。生成元の両端を同じ対象と仮定しない。 -/
def term : List I → D → D → Complex A
  | [], x, y => homObject A D x y
  | i :: w, x, y => homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ term w (C.target i) y)

/-- 指定生成元を、その両端の単位とともに一生成元pathへ入れる。 -/
def generatorTerm (i : I) : C.generator A D I i ⟶ C.term A D I [i] (C.source i) (C.target i) :=
  (λ_ (C.generator A D I i)).inv ≫
    (eId (Complex A) (C.source i) ⊗ₘ
      ((ρ_ (C.generator A D I i)).inv ≫
        (𝟙 (C.generator A D I i) ⊗ₘ eId (Complex A) (C.target i))))

lemma term_kFlat (hD : localHomKFlat A D) (w : List I) (x y : D) :
    complexKFlat A (C.term A D I w x y) := by
  induction w generalizing x y with
  | nil => exact hD x y
  | cons i w ih =>
    exact complexKFlat_tensor A (hD x (C.source i))
      (complexKFlat_tensor A (complexSphere_kFlat A (C.degree i)) (ih (C.target i) y))

variable [Small.{u} I]

abbrev internalHom (x y : D) : Complex A := ∐ (fun w : List I => C.term A D I w x y)

def inclusion (w : List I) (x y : D) : C.term A D I w x y ⟶ C.internalHom A D I x y :=
  Sigma.ι (fun w : List I => C.term A D I w x y) w

def originalHom (x y : D) : homObject A D x y ⟶ C.internalHom A D I x y :=
  C.inclusion A D I [] x y

def generatorInclusion (i : I) :
    C.generator A D I i ⟶ C.internalHom A D I (C.source i) (C.target i) :=
  C.generatorTerm A D I i ≫ C.inclusion A D I [i] (C.source i) (C.target i)

lemma internalHom_ext (x y : D) {T : Complex A}
    (f g : C.internalHom A D I x y ⟶ T)
    (h : ∀ w, C.inclusion A D I w x y ≫ f = C.inclusion A D I w x y ≫ g) : f = g :=
  Sigma.hom_ext f g h

lemma internalHom_kFlat (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.internalHom A D I x y) := by
  have : HasExactColimitsOfShape (Discrete (List I)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (List I)).symm)
  exact complexKFlat_colimit A (Discrete.functor fun w : List I => C.term A D I w x y)
    (fun w => C.term_kFlat A D I hD w.as x y)

end Family

/-- 増大関手のホモロジー核を消すために使う全境界cellの族。 -/
def boundaryFamily (E : Type z) [DGCategory A E] (F : DGFunctor A D E) :
    Family A D (DGCategoryBoundaryCells.Index A D E F) where
  source i := i.1
  target i := i.2.1
  degree i := i.2.2.degree
  boundary i := i.2.2.cycle

end SerrePositivity.DifferentialGraded.DGCellAttachment
end

end Paths

/-! ## PathEquations（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathEquations.lean） -/

/-! # cell path項の計算式

## 概要
未知の後続語の再帰定義を展開せず、先頭一段だけを計算する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathEquations
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma term_nil (x y : D) : C.term A D I [] x y = homObject A D x y := rfl

lemma term_cons (b : I) (w : List I) (x y : D) :
    C.term A D I (b :: w) x y = homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) := rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PathEquations

/-! ## PathComposition（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathComposition.lean） -/

/-! # 生成cellのpathと既存Homの合成

## 概要
生成元の順を保ち、隣り合う既存Homだけを豊穣合成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathComposition
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

def prependMap : ∀ (w : List I) (x y z : D),
    homObject A D x y ⊗ C.term A D I w y z ⟶ C.term A D I w x z
  | [], x, y, z => eComp (Complex A) x y z
  | i :: w, x, y, z =>
    (α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ⊗ₘ
        𝟙 (C.generator A D I i ⊗ C.term A D I w (C.target i) z))

def appendMap : ∀ (w z : List I) (x y t : D),
    C.term A D I w x y ⊗ C.term A D I z y t ⟶ C.term A D I (w ++ z) x t
  | [], z, x, y, t => C.prependMap A D I z x y t
  | i :: w, z, x, y, t =>
    (α_ (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.term A D I z y t)).hom ≫
    (homObject A D x (C.source i)) ◁
      ((α_ (C.generator A D I i) (C.term A D I w (C.target i) y)
        (C.term A D I z y t)).hom ≫
        (C.generator A D I i) ◁ appendMap w z (C.target i) y t)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PathComposition

/-! ## PathAction（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathAction.lean） -/

/-! # cell pathの先頭Hom作用の結合・単位・全次数自然性

## 概要
cell pathの先頭Hom作用の結合・単位・全次数自然性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma prependMap_assoc (w : List I) (x y z t : D) :
    (eComp (Complex A) x y z ▷ C.term A D I w z t) ≫ C.prependMap A D I w x z t =
    (α_ (homObject A D x y) (homObject A D y z) (C.term A D I w z t)).hom ≫
      (homObject A D x y) ◁ C.prependMap A D I w y z t ≫ C.prependMap A D I w x y t := by
  cases w with
  | nil => exact (e_assoc' (Complex A) x y z t).symm
  | cons i w =>
    simpa only [prependMap, term, tensorHom_id] using
      tensorJoin_assoc (homObject A D x y) (homObject A D y z) (homObject A D z (C.source i))
        (homObject A D x z) (homObject A D y (C.source i)) (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) t)
        (eComp (Complex A) x y z) (eComp (Complex A) y z (C.source i))
        (eComp (Complex A) x z (C.source i)) (eComp (Complex A) x y (C.source i))
        (e_assoc' (Complex A) x y z (C.source i)).symm

lemma prependMap_left_unit (w : List I) (x y : D) :
    (λ_ (C.term A D I w x y)).inv ≫ eId (Complex A) x ▷ C.term A D I w x y ≫
      C.prependMap A D I w x x y = 𝟙 (C.term A D I w x y) := by
  cases w with
  | nil => exact e_id_comp (Complex A) x y
  | cons i w =>
    simpa only [prependMap, term, tensorHom_id] using
      tensorJoin_left_unit (homObject A D x x) (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) (eId (Complex A) x)
        (eComp (Complex A) x x (C.source i)) (e_id_comp (Complex A) x (C.source i))

lemma prependMap_tail_cochain (i : I) (w w' : List I) (x y z : D)
    (p : ℤ) (f : Cochain (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) p) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
      ((tensorLeftHom (homObject A D x (C.source i)) _ _).f p f) (zero_add p) =
    ((tensorLeftHom (homObject A D x y) _ _).f p
      ((tensorLeftHom (homObject A D y (C.source i)) _ _).f p f)).comp
      (Cochain.ofHom (C.prependMap A D I (i :: w') x y z)) (add_zero p) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ (eComp (Complex A) x y (C.source i)) p f

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PathAction

/-! ## GeneratorAppend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/GeneratorAppend.lean） -/

/-! # 別端点を持つ一生成元pathの連結と単位因子の消去

## 概要
別端点を持つ一生成元pathの連結と単位因子の消去。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section GeneratorAppend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma generatorTerm_append (i : I) (w : List I) (y : D) :
    (C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
      C.appendMap A D I [i] w (C.source i) (C.target i) y =
    (λ_ (C.generator A D I i ⊗ C.term A D I w (C.target i) y)).inv ≫
      eId (Complex A) (C.source i) ▷ (C.generator A D I i ⊗ C.term A D I w (C.target i) y) := by
  simpa only [generatorTerm, appendMap, List.nil_append, term_nil] using
    tensorSandwich_append_distinct (C.generator A D I i)
      (homObject A D (C.source i) (C.source i)) (homObject A D (C.target i) (C.target i))
      (C.term A D I w (C.target i) y) (eId (Complex A) (C.source i)) (eId (Complex A) (C.target i))
      (C.prependMap A D I w (C.target i) (C.target i) y)
      (C.prependMap_left_unit A D I w (C.target i) y)

lemma prependMap_generatorTerm_append (i : I) (w : List I) (x y : D) :
    (homObject A D x (C.source i)) ◁
      ((C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
        C.appendMap A D I [i] w (C.source i) (C.target i) y) ≫
      C.prependMap A D I (i :: w) x (C.source i) y = 𝟙 (C.term A D I (i :: w) x y) := by
  rw [generatorTerm_append]
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_right_unit (homObject A D x (C.source i))
      (homObject A D (C.source i) (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (eId (Complex A) (C.source i)) (eComp (Complex A) x (C.source i) (C.source i))
      (e_comp_id (Complex A) x (C.source i))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end GeneratorAppend

/-! ## BoundaryCochain（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryCochain.lean） -/

/-! # 任意次数の生成cellを指定境界へ送る次数+1 cochain

## 概要
任意次数の生成cellを指定境界へ送る次数+1 cochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryCochain
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 次数qの生成元を次数q+1の指定境界へ送る。 -/
def boundaryCochain (i : I) :
    Cochain (C.generator A D I i) (homObject A D (C.source i) (C.target i)) 1 :=
  Cochain.fromSingleMk
    (moduleElementMap A ((homObject A D (C.source i) (C.target i)).X (C.degree i + 1))
      (C.boundary i).val) rfl

lemma boundaryCochain_closed (i : I) : δ 1 2 (C.boundaryCochain A D I i) = 0 := by
  rw [boundaryCochain, Cochain.δ_fromSingleMk _ _ 2 (C.degree i + 1 + 1) (by omega)]
  have h : moduleElementMap A _ (C.boundary i).val ≫
      (homObject A D (C.source i) (C.target i)).d (C.degree i + 1) (C.degree i + 1 + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (homObject A D (C.source i) (C.target i)).d
      (C.degree i + 1) (C.degree i + 1 + 1) (a • (C.boundary i).val) = 0
    rw [map_smul, (C.boundary i).property, smul_zero]
  rw [h, Cochain.fromSingleMk_zero]

lemma boundaryCochain_generator (i : I) :
    (C.boundaryCochain A D I i).v (C.degree i) (C.degree i + 1) rfl
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
      (C.boundary i).val := by
  rw [boundaryCochain, Cochain.fromSingleMk_v]
  change (moduleElementMap A _ (C.boundary i).val)
    (((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  exact one_smul A (C.boundary i).val

/-- 左右の複体の間で指定境界を挿入する。左因子を通るKoszul符号を保持する。 -/
def replaceMiddle (i : I) (P Q : Complex A) :
    Cochain (P ⊗ (C.generator A D I i ⊗ Q))
      (P ⊗ (homObject A D (C.source i) (C.target i) ⊗ Q)) 1 :=
  (tensorLeftHom P _ _).f 1
    ((tensorRightHom Q _ _).f 1 (C.boundaryCochain A D I i))

lemma replaceMiddle_closed (i : I) (P Q : Complex A) :
    δ 1 2 (C.replaceMiddle A D I i P Q) = 0 :=
  homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (C.boundaryCochain_closed A D I i))

/-- 境界挿入は先行する左因子の次数pに対し(-1)^pを伴う。生成元自身の次数は任意。 -/
lemma replaceMiddle_apply (i : I) (P Q : Complex A) (p q a : ℤ)
    (ha : p + (C.degree i + q) = a) (x : P.X p)
    (e : (C.generator A D I i).X (C.degree i)) (y : Q.X q) :
    (C.replaceMiddle A D I i P Q).v a (a + 1) rfl
      (ιTensorObj P (C.generator A D I i ⊗ Q) p (C.degree i + q) a ha
        (x ⊗ₜ[A] ιTensorObj (C.generator A D I i) Q (C.degree i) q (C.degree i + q) rfl
          (e ⊗ₜ[A] y))) =
    p.negOnePow • ιTensorObj P (homObject A D (C.source i) (C.target i) ⊗ Q)
      p (C.degree i + q + 1) (a + 1) (by omega)
      (x ⊗ₜ[A] ιTensorObj (homObject A D (C.source i) (C.target i)) Q
        (C.degree i + 1) q (C.degree i + q + 1) (by omega)
        ((C.boundaryCochain A D I i).v (C.degree i) (C.degree i + 1) rfl e ⊗ₜ[A] y)) := by
  rw [replaceMiddle, tensorLeftHom_apply_of_sum P (C.generator A D I i ⊗ Q)
    (homObject A D (C.source i) (C.target i) ⊗ Q) 1 p (C.degree i + q) a
      (C.degree i + q + 1) (a + 1) ha rfl rfl, one_mul, tensorRightHom_apply]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryCochain

/-! ## BoundaryFaces（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryFaces.lean） -/

/-! # 各有限pathで一つの生成元を指定境界へ置換するcochain

## 概要
各有限pathで一つの生成元を指定境界へ置換するcochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryFaces
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 先頭生成元を境界へ置き換え、左の既存Homと豊穣合成する。 -/
def replaceFirst (i : I) (w : List I) (x y : D) :
    Cochain (C.term A D I (i :: w) x y) (C.term A D I w x y) 1 :=
  (C.replaceMiddle A D I i (homObject A D x (C.source i))
      (C.term A D I w (C.target i) y)).comp
    (Cochain.ofHom
      ((α_ (homObject A D x (C.source i)) (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)).inv ≫
        (eComp (Complex A) x (C.source i) (C.target i) ▷ C.term A D I w (C.target i) y) ≫
        C.prependMap A D I w x (C.target i) y)) (add_zero 1)

lemma replaceFirst_closed (i : I) (w : List I) (x y : D) :
    δ 1 2 (C.replaceFirst A D I i w x y) = 0 := by
  rw [replaceFirst, δ_comp_ofHom, replaceMiddle_closed]
  exact Cochain.zero_comp _ _

/-- i番目の生成元を境界へ置換する。範囲外の添字は零。 -/
def replaceFace : ∀ (w : List I) (i : ℕ) (x y : D),
    Cochain (C.term A D I w x y) (C.term A D I (w.eraseIdx i) x y) 1
  | [], _, _, _ => 0
  | i :: w, 0, x, y => C.replaceFirst A D I i w x y
  | i :: w, j + 1, x, y =>
    (tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      ((tensorLeftHom (C.generator A D I i) _ _).f 1 (replaceFace w j (C.target i) y))

lemma replaceFace_closed (w : List I) (i : ℕ) (x y : D) :
    δ 1 2 (C.replaceFace A D I w i x y) = 0 := by
  induction w generalizing i x y with
  | nil => exact δ_zero _ _
  | cons j w ih =>
    cases i with
    | zero => exact C.replaceFirst_closed A D I j w x y
    | succ i => exact homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (ih i (C.target j) y))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryFaces

/-! ## BoundaryOperator（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryOperator.lean） -/

/-! # 全path上の指定境界置換作用素

## 概要
各生成元を境界に置換する有限和を、閉じた次数+1の自己cochainへ貼り合わせる。
この段階では二乗零と最終合成のLeibnizはまだ主張しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryOperator
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def replaceSummand (w : List I) (i : ℕ) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
  (C.replaceFace A D I w i x y).comp
    (Cochain.ofHom (C.inclusion A D I (w.eraseIdx i) x y)) (add_zero 1)

lemma replaceSummand_closed (w : List I) (i : ℕ) (x y : D) :
    δ 1 2 (C.replaceSummand A D I w i x y) = 0 := by
  rw [replaceSummand, δ_comp_ofHom, replaceFace_closed]
  exact Cochain.zero_comp _ _

def replaceRow (w : List I) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
  ∑ i ∈ Finset.range w.length, C.replaceSummand A D I w i x y

lemma replaceRow_closed (w : List I) (x y : D) :
    δ 1 2 (C.replaceRow A D I w x y) = 0 := by
  change (δ_hom ℤ _ _ 1 2) (C.replaceRow A D I w x y) = 0
  simp only [replaceRow, map_sum, δ_hom_apply, replaceSummand_closed, Finset.sum_const_zero]

lemma replaceRow_nil (x y : D) : C.replaceRow A D I [] x y = 0 := by simp [replaceRow]

def replacementToShift (x y : D) :
    C.internalHom A D I x y ⟶ (C.internalHom A D I x y)⟦(1 : ℤ)⟧ :=
  Sigma.desc (fun w : List I => Cocycle.equivHomShift.symm
    (Cocycle.mk (C.replaceRow A D I w x y) 2 (by omega) (C.replaceRow_closed A D I w x y)))

def replacement (x y : D) : Cochain (C.internalHom A D I x y) (C.internalHom A D I x y) 1 :=
  (Cocycle.equivHomShift (C.replacementToShift A D I x y)).val

lemma replacement_closed (x y : D) : δ 1 2 (C.replacement A D I x y) = 0 :=
  Cocycle.δ_eq_zero _ _

lemma replacement_precomp (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp (C.replacement A D I x y) (zero_add 1) =
      C.replaceRow A D I w x y := by
  have h : C.inclusion A D I w x y ≫ C.replacementToShift A D I x y =
      Cocycle.equivHomShift.symm (Cocycle.mk (C.replaceRow A D I w x y) 2
        (by omega) (C.replaceRow_closed A D I w x y)) := Sigma.ι_comp_desc _ _
  have hc := congrArg (fun f => (Cocycle.equivHomShift f).val) h
  rw [Cocycle.equivHomShift_comp, AddEquiv.apply_symm_apply] at hc
  exact hc

lemma replacement_originalHom (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp (C.replacement A D I x y) (zero_add 1) = 0 :=
  (C.replacement_precomp A D I [] x y).trans (C.replaceRow_nil A D I x y)

/-- 二重置換を各pathに制限すると、最初のfaceと短いpathの置換和になる。 -/
lemma replacement_square_precomp (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) =
    ∑ i ∈ Finset.range w.length, (C.replaceFace A D I w i x y).comp
      (C.replaceRow A D I (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, replacement_precomp]
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
    { toFun := fun f => f.comp (C.replacement A D I x y) (by omega)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (C.replaceRow A D I w x y) = _
  rw [replaceRow, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (C.replaceSummand A D I w i x y).comp (C.replacement A D I x y) (by omega) = _
  rw [replaceSummand, Cochain.comp_assoc_of_second_is_zero_cochain, replacement_precomp]

lemma replacement_square_originalHom (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, replacement_originalHom]
  exact Cochain.zero_comp _ _

lemma replacement_square_singleton (i : I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I [i] x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) = 0 := by
  rw [replacement_square_precomp]
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one, Finset.sum_singleton]
  change (C.replaceFirst A D I i [] x y).comp (C.replaceRow A D I [] x y) (by omega) = 0
  rw [replaceRow_nil]
  exact Cochain.comp_zero _ _

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryOperator

/-! ## BoundaryInterchange（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryInterchange.lean） -/

/-! # 指定境界の挿入と後方の次数+1 cochainの反交換

## 概要
指定境界の挿入と後方の次数+1 cochainの反交換。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryInterchange
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 指定境界への置換と後方作用の順序を交換すると負号が付く。
生成元の次数は任意で、両作用素の次数+1からこの負号が出る。 -/
lemma replaceMiddle_tail_anticommute (i : I) (K P Q : Complex A) (f : Cochain P Q 1) :
    (C.replaceMiddle A D I i K P).comp
      ((tensorLeftHom K _ _).f 1
        ((tensorLeftHom (homObject A D (C.source i) (C.target i)) P Q).f 1 f))
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K _ _).f 1
      ((tensorLeftHom (C.generator A D I i) P Q).f 1 f)).comp
      (C.replaceMiddle A D I i K Q) (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorLeftHom_cochain_anticommute K _ _ _ _ 1 1 2 (by omega) (by omega) _ _ _ _
    (tensorCochain_odd_anticommute (C.generator A D I i)
      (homObject A D (C.source i) (C.target i)) P Q (C.boundaryCochain A D I i) f)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryInterchange

/-! ## BoundaryHead（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryHead.lean） -/

/-! # 指定境界を左端へ挿入する表示と先頭Hom作用

## 概要
指定境界を左端へ挿入する表示と先頭Hom作用。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryHead
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

def replaceHead (i : I) (w : List I) (y : D) :
    Cochain (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.term A D I w (C.source i) y) 1 :=
  ((tensorRightHom (C.term A D I w (C.target i) y) _ _).f 1
    (C.boundaryCochain A D I i)).comp
    (Cochain.ofHom (C.prependMap A D I w (C.source i) (C.target i) y)) (add_zero 1)

lemma replaceHead_closed (i : I) (w : List I) (y : D) :
    δ 1 2 (C.replaceHead A D I i w y) = 0 := by
  rw [replaceHead, δ_comp_ofHom]
  have h := homComplexMap_closed
    (tensorRightHom (C.term A D I w (C.target i) y) (C.generator A D I i)
      (homObject A D (C.source i) (C.target i))) 1
    (C.boundaryCochain A D I i) (C.boundaryCochain_closed A D I i)
  change δ 1 2 ((tensorRightHom (C.term A D I w (C.target i) y) (C.generator A D I i)
    (homObject A D (C.source i) (C.target i))).f 1 (C.boundaryCochain A D I i)) = 0 at h
  rw [h]
  exact Cochain.zero_comp _ _

/-- 先頭置換を、左端での置換と元のHom作用へ分解する。 -/
lemma replaceFirst_eq_head (i : I) (w : List I) (x y : D) :
    C.replaceFirst A D I i w x y =
    ((tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      (C.replaceHead A D I i w y)).comp
      (Cochain.ofHom (C.prependMap A D I w x (C.source i) y)) (add_zero 1) := by
  have hc : (α_ (homObject A D x (C.source i))
      (homObject A D (C.source i) (C.target i)) (C.term A D I w (C.target i) y)).inv ≫
      (eComp (Complex A) x (C.source i) (C.target i) ▷ C.term A D I w (C.target i) y) ≫
      C.prependMap A D I w x (C.target i) y =
      (homObject A D x (C.source i)) ◁ C.prependMap A D I w (C.source i) (C.target i) y ≫
      C.prependMap A D I w x (C.source i) y := by
    rw [C.prependMap_assoc A D I w x (C.source i) (C.target i) y, Iso.inv_hom_id_assoc]
  rw [replaceFirst, hc, replaceHead, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

attribute [local irreducible] replaceHead replaceFirst

lemma prependMap_replaceHead (i : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
    ((tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      (C.replaceHead A D I i w z)) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1
      ((tensorLeftHom (homObject A D y (C.source i)) _ _).f 1
        (C.replaceHead A D I i w z))).comp
    (Cochain.ofHom ((α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.term A D I w (C.source i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ▷ C.term A D I w (C.source i) z))) (add_zero 1) := by
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y)
      (homObject A D y (C.source i)) (homObject A D x (C.source i)) _ _
      (eComp (Complex A) x y (C.source i)) 1 (C.replaceHead A D I i w z)

/-- 先頭Homの合成は先頭生成元の境界置換とも可換する。 -/
lemma prependMap_replaceFirst (i : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
      (C.replaceFirst A D I i w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1 (C.replaceFirst A D I i w y z)).comp
      (Cochain.ofHom (C.prependMap A D I w x y z)) (add_zero 1) := by
  have hc : (α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.term A D I w (C.source i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ▷ C.term A D I w (C.source i) z) ≫
      C.prependMap A D I w x (C.source i) z =
      (homObject A D x y) ◁ C.prependMap A D I w y (C.source i) z ≫
      C.prependMap A D I w x y z := by
    rw [C.prependMap_assoc A D I w x y (C.source i) z, Iso.inv_hom_id_assoc]
  rw [replaceFirst_eq_head, replaceFirst_eq_head]
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_action_cochain (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ _ _ 1 (C.replaceHead A D I i w z)
      (eComp (Complex A) x y (C.source i))
      (C.prependMap A D I w x (C.source i) z) (C.prependMap A D I w y (C.source i) z)
      (C.prependMap A D I w x y z) hc

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryHead

/-! ## BoundaryNaturality（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryNaturality.lean） -/

/-! # 全位置の境界置換と既存Hom作用の可換性

## 概要
全位置の境界置換と既存Hom作用の可換性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma replaceFace_nil (j : ℕ) (x y : D) : C.replaceFace A D I [] j x y = 0 := rfl

lemma replaceFace_zero (i : I) (w : List I) (x y : D) :
    C.replaceFace A D I (i :: w) 0 x y = C.replaceFirst A D I i w x y := rfl

lemma replaceFace_succ (i : I) (w : List I) (j : ℕ) (x y : D) :
    C.replaceFace A D I (i :: w) (j + 1) x y =
    (tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      ((tensorLeftHom (C.generator A D I i) _ _).f 1
        (C.replaceFace A D I w j (C.target i) y)) := rfl

attribute [local irreducible] replaceFace

lemma prependMap_tail_hom (i : I) (w w' : List I) (x y z : D) :
    (tensorLeftHom (homObject A D y (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
      tensorLeftHom (homObject A D x y) (C.term A D I (i :: w) y z)
        (C.term A D I (i :: w') y z)) ≫
      homPostcompose (homObject A D x y ⊗ C.term A D I (i :: w) y z)
        (C.prependMap A D I (i :: w') x y z) =
    tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
      homPrecompose (C.prependMap A D I (i :: w) x y z) (C.term A D I (i :: w') x z) := by
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_hom_naturality (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ (eComp (Complex A) x y (C.source i))

lemma prependMap_suffix_hom (i : I) (w w' : List I) (x y z : D) :
    tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) z)
      (C.term A D I w' (C.target i) z) ≫
      ((tensorLeftHom (homObject A D y (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
        (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
        tensorLeftHom (homObject A D x y) (C.term A D I (i :: w) y z)
          (C.term A D I (i :: w') y z)) ≫
        homPostcompose (homObject A D x y ⊗ C.term A D I (i :: w) y z)
          (C.prependMap A D I (i :: w') x y z)) =
    tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) z)
      (C.term A D I w' (C.target i) z) ≫
      (tensorLeftHom (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
        (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
        homPrecompose (C.prependMap A D I (i :: w) x y z) (C.term A D I (i :: w') x z)) := by
  rw [prependMap_tail_hom]

lemma prependMap_replaceFace (w : List I) (j : ℕ) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp
      (C.replaceFace A D I w j x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1 (C.replaceFace A D I w j y z)).comp
      (Cochain.ofHom (C.prependMap A D I (w.eraseIdx j) x y z)) (add_zero 1) := by
  cases w with
  | nil => simp only [replaceFace_nil, map_zero, Cochain.comp_zero, Cochain.zero_comp]
  | cons i w =>
    cases j with
    | zero =>
      rw [replaceFace_zero, replaceFace_zero]
      exact C.prependMap_replaceFirst A D I i w x y z
    | succ j =>
      have h := congrArg (fun t : homComplex A (C.term A D I w (C.target i) z)
          (C.term A D I (w.eraseIdx j) (C.target i) z) ⟶
          homComplex A (homObject A D x y ⊗ C.term A D I (i :: w) y z)
            (C.term A D I (i :: w.eraseIdx j) x z) =>
          t.f 1 (C.replaceFace A D I w j (C.target i) z))
        (C.prependMap_suffix_hom A D I i w (w.eraseIdx j) x y z)
      simp only [chain_comp_apply, homPostcompose_apply] at h
      rw [replaceFace_succ, replaceFace_succ]
      exact h.symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryNaturality

/-! ## BoundaryHeadInterchange（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryHeadInterchange.lean） -/

/-! # 先頭生成元と任意後方生成元の境界置換の反交換

## 概要
先頭生成元と任意後方生成元の境界置換の反交換。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryHeadInterchange
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)
attribute [local irreducible] replaceHead replaceFirst replaceFace

lemma replaceHead_face_anticommute (i : I) (w : List I) (j : ℕ) (y : D) :
    (C.replaceHead A D I i w y).comp (C.replaceFace A D I w j (C.source i) y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom (C.generator A D I i) _ _).f 1
      (C.replaceFace A D I w j (C.target i) y)).comp
      (C.replaceHead A D I i (w.eraseIdx j) y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [replaceHead, replaceHead, Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_replaceFace, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    tensorCochain_odd_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

lemma replaceFirst_face_anticommute (i : I) (w : List I) (j : ℕ) (x y : D) :
    (C.replaceFirst A D I i w x y).comp (C.replaceFace A D I w j x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -((C.replaceFace A D I (i :: w) (j + 1) x y).comp
      (C.replaceFirst A D I i (w.eraseIdx j) x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [replaceFace_succ, replaceFirst_eq_head, replaceFirst_eq_head,
    Cochain.comp_assoc_of_second_is_zero_cochain, prependMap_replaceFace,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorLeftHom_cochain_comp, replaceHead_face_anticommute, map_neg,
    tensorLeftHom_cochain_comp, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryHeadInterchange

/-! ## DoubleFaces（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/DoubleFaces.lean） -/

/-! # 終域のpathも保持した二重境界置換の反交換

## 概要
終域のpathも保持した二重境界置換の反交換。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DoubleFaces
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma replaceFace_succ_comp (b : I) (w : List I) (i j : ℕ) (x y : D) :
    (C.replaceFace A D I (b :: w) (i + 1) x y).comp
      (C.replaceFace A D I ((b :: w).eraseIdx (i + 1)) (j + 1) x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    (tensorLeftHom (homObject A D x (C.source b)) _ _).f 2
      ((tensorLeftHom (C.generator A D I b) _ _).f 2
        ((C.replaceFace A D I w i (C.target b) y).comp
          (C.replaceFace A D I (w.eraseIdx i) j (C.target b) y) (by omega))) := by
  change (((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceFace A D I w i (C.target b) y))).comp
    ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceFace A D I (w.eraseIdx i) j (C.target b) y))) (by omega)) = _
  rw [← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp]

def DoubleFace (w : List I) (x y : D) :=
  Σ z : List I, Cochain (C.term A D I w x y) (C.term A D I z x y) 2

def doubleFace (w : List I) (i j : ℕ) (x y : D) : C.DoubleFace A D I w x y :=
  ⟨(w.eraseIdx i).eraseIdx j,
    (C.replaceFace A D I w i x y).comp (C.replaceFace A D I (w.eraseIdx i) j x y) (by omega)⟩

def negateDoubleFace {w : List I} {x y : D} :
    C.DoubleFace A D I w x y → C.DoubleFace A D I w x y
  | ⟨z, f⟩ => ⟨z, -f⟩

def prefixDoubleFace (b : I) (w : List I) (x y : D) :
    C.DoubleFace A D I w (C.target b) y → C.DoubleFace A D I (b :: w) x y
  | ⟨z, f⟩ => ⟨b :: z, (tensorLeftHom (homObject A D x (C.source b)) _ _).f 2
      ((tensorLeftHom (C.generator A D I b) _ _).f 2 f)⟩

lemma prefixDoubleFace_negate (b : I) (w : List I) (x y : D)
    (f : C.DoubleFace A D I w (C.target b) y) :
    C.prefixDoubleFace A D I b w x y (C.negateDoubleFace A D I f) =
      C.negateDoubleFace A D I (C.prefixDoubleFace A D I b w x y f) := by
  rcases f with ⟨z, f⟩
  simp only [prefixDoubleFace, negateDoubleFace, map_neg]

lemma doubleFace_cons_succ (b : I) (w : List I) (i j : ℕ) (x y : D) :
    C.doubleFace A D I (b :: w) (i + 1) (j + 1) x y =
      C.prefixDoubleFace A D I b w x y (C.doubleFace A D I w i j (C.target b) y) := by
  exact congrArg (fun f => (⟨b :: (w.eraseIdx i).eraseIdx j, f⟩ :
    C.DoubleFace A D I (b :: w) x y)) (C.replaceFace_succ_comp A D I b w i j x y)

lemma doubleFace_cons_zero (b : I) (w : List I) (j : ℕ) (x y : D) :
    C.doubleFace A D I (b :: w) 0 j x y =
      C.negateDoubleFace A D I (C.doubleFace A D I (b :: w) (j + 1) 0 x y) := by
  exact congrArg (fun f => (⟨w.eraseIdx j, f⟩ : C.DoubleFace A D I (b :: w) x y))
    (C.replaceFirst_face_anticommute A D I b w j x y)

lemma doubleFace_swap_of_le (w : List I) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    C.doubleFace A D I w i j x y =
      C.negateDoubleFace A D I (C.doubleFace A D I w (j + 1) i x y) := by
  induction w generalizing i j x y with
  | nil => simp only [doubleFace, List.eraseIdx_nil, replaceFace_nil,
      Cochain.zero_comp, negateDoubleFace, neg_zero]
  | cons b w ih =>
    cases i with
    | zero => exact C.doubleFace_cons_zero A D I b w j x y
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        rw [doubleFace_cons_succ, doubleFace_cons_succ, ← prefixDoubleFace_negate]
        exact congrArg (C.prefixDoubleFace A D I b w x y) (ih i j (by omega) (C.target b) y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end DoubleFaces

/-! ## DoubleFaceSum（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/DoubleFaceSum.lean） -/

/-! # 二重境界置換の全path直和への包含と有限和の相殺

## 概要
二重境界置換の全path直和への包含と有限和の相殺。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DoubleFaceSum
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def includeDoubleFace {w : List I} {x y : D} :
    C.DoubleFace A D I w x y → Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2
  | ⟨z, f⟩ => f.comp (Cochain.ofHom (C.inclusion A D I z x y)) (add_zero 2)

lemma includeDoubleFace_negate {w : List I} {x y : D} (f : C.DoubleFace A D I w x y) :
    C.includeDoubleFace A D I (C.negateDoubleFace A D I f) = -C.includeDoubleFace A D I f := by
  rcases f with ⟨z, f⟩
  simp only [includeDoubleFace, negateDoubleFace, Cochain.neg_comp]

def replacementPair (w : List I) (i j : ℕ) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
  C.includeDoubleFace A D I (C.doubleFace A D I w i j x y)

lemma replacementPair_swap_of_le (w : List I) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    C.replacementPair A D I w i j x y = -C.replacementPair A D I w (j + 1) i x y := by
  exact (congrArg (C.includeDoubleFace A D I)
    (C.doubleFace_swap_of_le A D I w i j hij x y)).trans (C.includeDoubleFace_negate A D I _)

lemma replacementPair_swap (w : List I) (i j : ℕ) (x y : D) :
    C.replacementPair A D I w i j x y =
    -C.replacementPair A D I w (DGQuotient.swapErasure (i, j)).1
      (DGQuotient.swapErasure (i, j)).2 x y := by
  by_cases hij : j < i
  · have h := C.replacementPair_swap_of_le A D I w j (i - 1) (by omega) x y
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at h
    simp only [DGQuotient.swapErasure, ite_eq_left hij]
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · simpa only [DGQuotient.swapErasure, Prod.fst, Prod.snd, ite_eq_right hij] using
      C.replacementPair_swap_of_le A D I w i j (by omega) x y

lemma replacementPair_double_sum_zero (w : List I) (x y : D) :
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      C.replacementPair A D I w i j x y = 0 :=
  DGQuotient.erasure_double_sum_cancel w.length (fun i j => C.replacementPair A D I w i j x y)
    (fun i _ j _ => C.replacementPair_swap A D I w i j x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end DoubleFaceSum

/-! ## PrimitiveData（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrimitiveData.lean） -/

/-! # cell付加の関手延長に指定する原始元とその評価cochain

## 概要
cell付加の関手延長に指定する原始元とその評価cochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrimitiveData
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I) (E : Type z) [DGCategory A E] (F : DGFunctor A D E)

/-- 各cellの像を指定し、微分が元の境界の像になることを要求する。 -/
structure PrimitiveData where
  primitive : ∀ i, (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).X (C.degree i)
  boundary : ∀ i, (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).d
    (C.degree i) (C.degree i + 1) (primitive i) =
      (F.map (C.source i) (C.target i)).f (C.degree i + 1) (C.boundary i).val

namespace PrimitiveData
variable {A D I C E F} (P : PrimitiveData A D I C E F)

/-- 原始元は一般に閉じていないため、まず次数0 cochainとして評価する。 -/
def cochain (i : I) : Cochain (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i))) 0 :=
  Cochain.fromSingleMk (p := C.degree i) (q := C.degree i)
    (moduleElementMap A _ (P.primitive i)) (add_zero _)

lemma cochain_generator (i : I) :
    (P.cochain i).v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    P.primitive i := by
  rw [cochain, Cochain.fromSingleMk_v]
  change (moduleElementMap A _ (P.primitive i))
    (((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  exact one_smul A (P.primitive i)

/-- 原始元評価の微分は指定境界の関手像。 -/
lemma cochain_differential (i : I) :
    δ 0 1 (P.cochain i) = (C.boundaryCochain A D I i).comp
      (Cochain.ofHom (F.map (C.source i) (C.target i))) (add_zero 1) := by
  rw [cochain, Cochain.δ_fromSingleMk _ _ 1 (C.degree i + 1) (by omega),
    boundaryCochain, ← Cochain.fromSingleMk_postcomp]
  congr 1
  apply (moduleElementEquiv A _).injective
  change (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).d
    (C.degree i) (C.degree i + 1) ((1 : A) • P.primitive i) =
    (F.map (C.source i) (C.target i)).f (C.degree i + 1) ((1 : A) • (C.boundary i).val)
  rw [one_smul, one_smul]
  exact P.boundary i

end PrimitiveData
end SerrePositivity.DifferentialGraded.DGCellAttachment.Family

namespace SerrePositivity.DifferentialGraded

namespace DGCategoryBoundaryCells
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type z) [DGCategory A E] (F : DGFunctor A D E)

/-- 全境界cellの族には、添字自身が持つ指定原始元がある。 -/
def primitiveData : Family.PrimitiveData A D (Index A D E F) (boundaryFamily A D E F) E F where
  primitive i := i.2.2.primitive
  boundary i := i.2.2.boundary

end DGCategoryBoundaryCells
end SerrePositivity.DifferentialGraded
end

end PrimitiveData

/-! ## PrimitiveAction（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrimitiveAction.lean） -/

/-! # 指定原始元の後方Homへの作用と境界作用

## 概要
指定原始元の後方Homへの作用と境界作用。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrimitiveAction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

def primitiveAction (i : I) (y : E) :
    Cochain (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) y)
      (homObject A E (F.obj (C.source i)) y) 0 :=
  ((tensorRightHom (homObject A E (F.obj (C.target i)) y) (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i)))).f 0 (P.cochain i)).comp
    (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y))
      (zero_add 0)

/-- 境界をFで写して後方Homと合成するchain map。 -/
def boundaryOriginalAction (_P : PrimitiveData A D I C E F) (i : I) (y : E) :
    homObject A D (C.source i) (C.target i) ⊗ homObject A E (F.obj (C.target i)) y ⟶
      homObject A E (F.obj (C.source i)) y :=
  (F.map (C.source i) (C.target i) ▷ homObject A E (F.obj (C.target i)) y) ≫
    eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y

lemma primitiveAction_differential (i : I) (y : E) :
    δ 0 1 (P.primitiveAction i y) =
    ((tensorRightHom (homObject A E (F.obj (C.target i)) y) (C.generator A D I i)
      (homObject A D (C.source i) (C.target i))).f 1 (C.boundaryCochain A D I i)).comp
      (Cochain.ofHom (P.boundaryOriginalAction i y)) (add_zero 1) := by
  rw [primitiveAction, δ_comp_ofHom,
    homComplexMap_differential (tensorRightHom _ _ _) 0 1,
    cochain_differential, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma primitiveAction_evaluate (i : I) (y : E) (T : Complex A)
    (f : Cochain T (homObject A E (F.obj (C.target i)) y) 0) :
    (tensorZeroCochain (P.cochain i) f).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y))
        (zero_add 0) =
    ((tensorLeftHom (C.generator A D I i) T (homObject A E (F.obj (C.target i)) y)).f 0 f).comp
      (P.primitiveAction i y) (zero_add 0) := by
  have h := tensorCochain_interchange (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i)))
    T (homObject A E (F.obj (C.target i)) y) 0 0 0 (zero_add 0) (zero_add 0)
    (P.cochain i) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [tensorZeroCochain, h, Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end PrimitiveAction

/-! ## BoundarySquare（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundarySquare.lean） -/

/-! # 任意次数cellの全path上の境界置換作用素は二乗零

## 概要
任意次数cellの全path上の境界置換作用素は二乗零。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundarySquare
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma pathCochain_ext (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y) T p)
    (h : ∀ w : List I, (Cochain.ofHom (C.inclusion A D I w x y)).comp f (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (colimit.isColimit (Discrete.functor (fun w : List I => C.term A D I w x y)))).hom_ext
  intro w
  change (C.inclusion A D I w.as x y).f i ≫ f.v i n hn =
    (C.inclusion A D I w.as x y).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I w.as x y) T p => z.v i n hn) (h w.as)

lemma replacement_square_precomp_double_sum (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) =
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      C.replacementPair A D I w i j x y := by
  rw [replacement_square_precomp]
  apply Finset.sum_congr rfl
  intro i hi
  let R : Cochain (C.term A D I (w.eraseIdx i) x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
    { toFun := fun f => (C.replaceFace A D I w i x y).comp f (by omega)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  change R (C.replaceRow A D I (w.eraseIdx i) x y) = _
  rw [replaceRow, map_sum, List.length_eraseIdx_of_lt (Finset.mem_range.mp hi)]
  apply Finset.sum_congr rfl
  intro j _
  change (C.replaceFace A D I w i x y).comp
      ((C.replaceFace A D I (w.eraseIdx i) j x y).comp
        (Cochain.ofHom (C.inclusion A D I ((w.eraseIdx i).eraseIdx j) x y)) (add_zero 1))
      (show (1 : ℤ) + 1 = 2 by omega) =
    ((C.replaceFace A D I w i x y).comp (C.replaceFace A D I (w.eraseIdx i) j x y)
      (show (1 : ℤ) + 1 = 2 by omega)).comp
      (Cochain.ofHom (C.inclusion A D I ((w.eraseIdx i).eraseIdx j) x y)) (add_zero 2)
  exact (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _).symm

lemma replacement_square_zero (x y : D) :
    (C.replacement A D I x y).comp (C.replacement A D I x y)
      (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply C.pathCochain_ext A D I x y 2
  intro w
  rw [replacement_square_precomp_double_sum, replacementPair_double_sum_zero, Cochain.comp_zero]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundarySquare
