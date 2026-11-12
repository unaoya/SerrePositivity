module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTateTensorTrivial
public import SerrePositivity.EInfinity.PowerOperation.CyclicTateResolution
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# 左正則表現に平坦な自明係数を付けた周期複体の非輪状性

DAG XIII Proposition 2.2.3 の混合軌道の Tate 消滅の鎖レベルの補助。
指定周期微分のテンソル比較と、平坦係数のテンソルによる完全性の保存を使う。
特に F_p 上の任意の係数加群に適用できる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- 平坦な自明係数を付けた同じ左正則周期複体は全次数で完全。 -/
lemma cyclicTateComplex_regularTensor_exactAt (B : Rep.{u} k G) [B.IsTrivial]
    [Module.Flat k B] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℤ) :
    (cyclicTateComplex (Rep.leftRegular k G ⊗ B) g).ExactAt i := by
  let P := cyclicTateComplex (Rep.leftRegular k G) g
  let J := forget₂ (Rep.{u} k G) (ModuleCat k)
  have hP : (P.sc' (i - 1) i (i + 1)).Exact :=
    (HomologicalComplex.exactAt_iff' _ _ i _ (by simp) (by simp)).mp
      (cyclicTateComplex_leftRegular_exactAt k g hg i)
  have h : (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P).ExactAt i := by
    rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    apply J.reflects_exact_of_faithful
    change (((P.sc' (i - 1) i (i + 1)).map J).map (tensorRight (J.obj B))).Exact
    exact Module.Flat.rTensor_shortComplex_exact (J.obj B) _ (hP.map J)
  exact h.of_iso (cyclicTateComplex_tensorTrivialIso (Rep.leftRegular k G) B g)

/-- 平坦な自明係数の誘導周期複体の全次数の非輪状性。 -/
lemma cyclicTateComplex_regularTensor_acyclic (B : Rep.{u} k G) [B.IsTrivial]
    [Module.Flat k B] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (cyclicTateComplex (Rep.leftRegular k G ⊗ B) g).Acyclic :=
  cyclicTateComplex_regularTensor_exactAt B g hg

/-- 体上では自明係数に平坦性の追加入力を置かずに適用できる。 -/
lemma cyclicTateComplex_regularTensor_acyclic_field {F : Type u} [Field F]
    (B : Rep.{u} F G) [B.IsTrivial] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (cyclicTateComplex (Rep.leftRegular F G ⊗ B) g).Acyclic :=
  cyclicTateComplex_regularTensor_acyclic B g hg

end SerrePositivity.EInfinity.PowerOperation
