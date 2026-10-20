module
public import SerrePositivity.KST.SConstruction.DGFunctorEnrichment
public import SerrePositivity.DifferentialGraded.Complexes.DiskGenerator

/-! # 全次数 Hom end の元の判定と自然性
概要：Hom end の斉次元を全対象の評価で判定し、全次数の自然性を回収する。
方針：disk の普遍性で chain map の判定に戻し、既存の符号つき自然性を適用する。
規約：閉零元への制限をしない。使われ方：横合成の符号つき交換律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]

/-- 全対象で評価が一致する元の斉次自然変換は等しい。 -/
lemma dgFunctorHomElement_ext {M N : DGFunctor A D E} {q : ℤ}
    {z w : (dgFunctorHom A D E M N).X q}
    (h : ∀ x : D, (dgFunctorHomπ A D E M N x).f q z =
      (dgFunctorHomπ A D E M N x).f q w) : z = w := by
  apply (complexDiskHomEquiv A (dgFunctorHom A D E M N) q).symm.injective
  apply dgFunctorHom_ext
  intro x
  apply (complexDiskHomEquiv A _ q).injective
  rw [complexDiskHomEquiv_naturality, complexDiskHomEquiv_naturality,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h x

/-- 全次数 Hom end の任意の斉次元が満たす元の符号つき自然性。 -/
lemma dgFunctorHomElement_naturality {M N : DGFunctor A D E} {x y : D}
    {q p n : ℤ} (z : (dgFunctorHom A D E M N).X q) (f : GradedHom A x y p)
    (hn : q + p = n) :
    (q * p).negOnePow • forward A ((M.map x y).f p f)
        ((dgFunctorHomπ A D E M N y).f q z) (by omega) =
      forward A ((dgFunctorHomπ A D E M N x).f q z) ((N.map x y).f p f) hn :=
  dgFunctorFamilyNaturality_apply A D E (dgFunctorHomπ A D E M N)
    (dgFunctorHomπ_naturality A D E M N) z f hn

end SerrePositivity.KST.SConstruction
