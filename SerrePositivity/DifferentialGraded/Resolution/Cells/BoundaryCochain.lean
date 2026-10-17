module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Paths
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
