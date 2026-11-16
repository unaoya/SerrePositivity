module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteComponents
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorComponents

/-!
# 有限頭部のテンソル比較の逆の次数成分

## 概要
有限個の指定行成分を元のテンソルへ戻す射を作る。

## 方針
指定行への挿入を線形射にし、テンソルの直和から降ろして有限和を取る。

## 規約
このファイルの定義の段階では、逆写像の等式を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部における比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped TensorProduct BigOperators

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 同じ指定行への挿入を、係数線形な射として使う。 -/
def insertMorphism (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n : ℕ) :
    (K.X n).X (q-n) ⟶ (total K).X q :=
  ModuleCat.ofHom ((componentsLinearEquiv K q).symm.toLinearMap.comp
    (LinearMap.single R (fun n : ℕ => (K.X n).X (q-n)) n))

/-- この射の評価は、元の指定成分への挿入そのものである。 -/
@[simp] theorem insertMorphism_apply (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n : ℕ)
    (x : (K.X n).X (q-n)) : insertMorphism K q n x = insert K q n x := rfl

/-- 挿入後の同じ成分への射影は恒等射である。 -/
@[reassoc (attr := simp)] theorem insertMorphism_component_self
    (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n : ℕ) :
    insertMorphism K q n ≫ componentπ K n q = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact insert_component_self K q n x

/-- 挿入後の異なる成分への射影は零射である。 -/
@[reassoc (attr := simp)] theorem insertMorphism_component_ne
    (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n m : ℕ) (h : m ≠ n) :
    insertMorphism K q n ≫ componentπ K m q = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact insert_component_ne K q n m h x

/-- 元のテンソルへ戻す、指定行の同次成分。 -/
def tensorInsertSummand (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (q : ℤ) (n : ℕ) (a t : ℤ) (h : a+t=q-n) :
    L.X a ⊗ (K.X n).X t ⟶ (cochainTensor L (total K)).X q :=
  interchangeSign a n • ((L.X a ◁
    ((eqToHom (by congr 1; omega) : (K.X n).X t ⟶ (K.X n).X ((q-a)-n)) ≫
      insertMorphism K (q-a) n)) ≫
        ιTensorObj L (total K) a (q-a) q (by omega))

/-- 指定行のテンソル複体の一つの次数から、元のテンソルの全次数へ戻す射。 -/
def tensorInsertRow (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (q : ℤ) (n : ℕ) : ((tensorRows L K).X n).X (q-n) ⟶ (cochainTensor L (total K)).X q :=
  Sigma.desc (fun ij : {ij : ℤ × ℤ // ij.1+ij.2=q-n} =>
    tensorInsertSummand L K q n ij.val.1 ij.val.2 ij.property)

/-- 指定行の戻す射を同次成分に制限すると、元の指定射になる。 -/
@[reassoc] theorem ι_tensorInsertRow (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (q : ℤ) (n : ℕ) (a t : ℤ) (h : a+t=q-n) :
    ιTensorObj L (K.X n) a t (q-n) h ≫ tensorInsertRow L K q n =
      tensorInsertSummand L K q n a t h := by
  change Sigma.ι (cochainTensorSummand L (K.X n) (q-n)) ⟨(a,t),h⟩ ≫ Sigma.desc _ = _
  rw [Sigma.ι_desc]

/-- 有限頭部の各行を足し合わせる、逆の候補となる次数ごとの射。 -/
def finiteTensorInverseDegree (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (N : ℕ) (q : ℤ) : (total (tensorRows L K)).X q ⟶ (cochainTensor L (total K)).X q :=
  ∑ n ∈ Finset.range N, componentπ (tensorRows L K) n q ≫ tensorInsertRow L K q n

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
