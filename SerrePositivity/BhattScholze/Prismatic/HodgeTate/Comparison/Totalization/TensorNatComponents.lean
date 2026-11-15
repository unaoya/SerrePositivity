module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorHomComponents
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorNaturalComparison

/-!
# 指定非負模型での標準比較の成分

## 概要
随伴で作った比較鎖写像の成分を、最初に定義した符号付き次数成分と同定する。

## 方針
零延長の指定行同型と逆を相殺し、転置と行の単位の符号を合わせる。

## 規約
比較射や積全複体の模型を置き換えない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の標準比較の検査。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped TensorProduct SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- Hom 複体の後合成を、元の指定同次成分で評価する。 -/
theorem homPostcompose_v_apply (L : Complex R) {P Q : Complex R} (f : P ⟶ Q)
    (b : ℤ) (z : Homogeneous L P b) (a q : ℤ) (h : a+b=q) (y : L.X a) :
    (((homPostcompose L f).f b z).v a q h) y = f.f q (z.v a q h y) := by
  change ((z.comp (Cochain.ofHom f) (add_zero b)).v a q h) y = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

set_option maxHeartbeats 800000 in
-- 零延長の単位と閉構造の型の照合に、単位の行成分の補題と同じ上限を使う。
/-- 同じ非負横次数の積全複体模型での、標準比較の指定同次成分。 -/
theorem tensorTotalComparison_component (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (a b q : ℤ) (hab : a+b=q) (n : ℕ) (x : (total K).X b) (y : L.X a) :
    componentπ (tensorRows L K) n q
      ((tensorTotalComparison L K).f q (ιTensorObj L (total K) a b q hab (y ⊗ₜ[R] x))) =
      (a * (n : ℤ)).negOnePow • ιTensorObj L (K.X n) a (b-n) (q-n) (by omega)
        (y ⊗ₜ[R] componentπ K n b x) := by
  let D := tensorRows L K
  let E := D.extend ComplexShape.embeddingUpNat
  let z := ((ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRowsNat L K)).f b x
  have hm := congrArg (fun f => f x)
    (ProductTotal.map_π (tensorUnitRowsNat L K) (n : ℤ) (b-n) b (by omega))
  simp only [ModuleCat.comp_apply] at hm
  rw [tensorUnitRowsNat_f_natCast] at hm
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hm
  change ProductTotal.π (((homFunctor L).mapHomologicalComplex (.up ℤ)).obj E)
      (n : ℤ) (b-n) b (by omega) z =
    (homPostcompose L (rowIso D n).inv).f (b-n)
      (((ihom.adjunction L).unit.app (K.X n)).f (b-n) (componentπ K n b x)) at hm
  have hi := congrArg (fun f => f y)
    (homTotalInverse_component L E b z a q hab (n : ℤ) (q-n) (by omega))
  simp only [ModuleCat.comp_apply] at hi
  rw [hm, homPostcompose_v_apply] at hi
  erw [tensorUnit_component L (K.X n) (b-n) a (q-n)
    (by omega) (componentπ K n b x) y] at hi
  have hc₀ := congrArg (fun t => (rowIso D n).hom.f (q-n) t) hi
  have hcancel := ModuleCat.hom_inv_apply
    ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) (q-n)).mapIso (rowIso D n))
    (((b-(n : ℤ))*a).negOnePow • ιTensorObj L (K.X n) a (b-n) (q-n) (by omega)
      (y ⊗ₜ[R] componentπ K n b x))
  have hc := hc₀.trans hcancel
  change componentπ D n q (((tensorTotalTransposeNat L K).f b x).v a q hab y) =
    ((b-(n : ℤ))*a).negOnePow • ιTensorObj L (K.X n) a (b-n) (q-n) (by omega)
      (y ⊗ₜ[R] componentπ K n b x) at hc
  have ht := tensorHomEquiv_component L (total K) (total D)
    (tensorTotalComparison L K) b a q hab x y
  rw [tensorTotalComparison_transpose] at ht
  have h := congrArg (fun t => componentπ D n q t) ht
  simp only [Units.smul_def, map_zsmul] at h
  change componentπ D n q (((tensorTotalTransposeNat L K).f b x).v a q hab y) =
    (b*a).negOnePow • componentπ D n q
      ((tensorTotalComparison L K).f q (ιTensorObj L (total K) a b q hab (y ⊗ₜ[R] x))) at h
  rw [hc] at h
  have hh := congrArg (fun v => (b*a).negOnePow • v) h
  simp only [smul_smul, Int.units_mul_self, one_smul] at hh
  rw [tensorTranspose_unit_sign] at hh
  exact hh.symm

/-- 随伴から作った鎖写像と、最初に指定した次数ごとの比較は同じ射である。 -/
theorem tensorTotalComparison_f_eq (L : Complex R) (K : CochainComplex (Complex R) ℕ) (q : ℤ) :
    (tensorTotalComparison L K).f q = tensorComparisonDegree L K q := by
  apply mapBifunctor.hom_ext
  intro a b hab
  change a+b=q at hab
  apply component_hom_ext
  intro n
  simp only [Category.assoc]
  rw [tensorComparisonDegree_component]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro y x
  change componentπ (tensorRows L K) n q
      ((tensorTotalComparison L K).f q (ιTensorObj L (total K) a b q hab (y ⊗ₜ[R] x))) =
    (a * (n : ℤ)).negOnePow • ((L.X a ◁ componentπ K n b) ≫
      ιTensorObj L (K.X n) a (b-n) (q-n) (by omega)) (y ⊗ₜ[R] x)
  rw [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  exact tensorTotalComparison_component L K a b q hab n x y

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
