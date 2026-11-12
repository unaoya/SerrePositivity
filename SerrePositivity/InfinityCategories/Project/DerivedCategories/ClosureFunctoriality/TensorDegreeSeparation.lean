module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Algebra.Homology.Monoidal

/-!
概要：複体 tensor の全次数直和で、指定した二次数の成分を射影する。
方針：total の余積普遍性から、他の二次数を零にする加群射を構成する。
規約：次数別の射影であり、微分と可換する複体射とは主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (K L : Complex R)

/-- tensor の指定二次数だけを読む次数別射影。 -/
def tensorDegreeProjection (p q n : ℤ) :
    (K ⊗ L).X n ⟶ K.X p ⊗ L.X q := by
  classical
  exact mapBifunctorDesc (fun i j _ =>
    if h : i = p ∧ j = q then eqToHom (by rw [h.1, h.2]; rfl) else 0)

/-- 指定二次数への包含は射影で分裂する。 -/
lemma tensorDegreeProjection_split (p q n : ℤ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ tensorDegreeProjection R K L p q n = 𝟙 _ := by
  classical
  unfold tensorDegreeProjection
  rw [ι_mapBifunctorDesc]
  simp

/-- 第一次数が異なる成分は射影で零になる。 -/
lemma tensorDegreeProjection_other (p q i j n : ℤ) (h : i + j = n) (hi : i ≠ p) :
    ιTensorObj K L i j n h ≫ tensorDegreeProjection R K L p q n = 0 := by
  classical
  unfold tensorDegreeProjection
  rw [ι_mapBifunctorDesc]
  simp [hi]

/-- tensor の各二次数成分の包含は、鎖の元として単射。 -/
lemma tensorDegreeInclusion_injective (p q n : ℤ) (h : p + q = n) :
    Function.Injective (ιTensorObj K L p q n h) := by
  intro a b hab
  have ha := ConcreteCategory.congr_hom (tensorDegreeProjection_split R K L p q n h) a
  have hb := ConcreteCategory.congr_hom (tensorDegreeProjection_split R K L p q n h) b
  change tensorDegreeProjection R K L p q n (ιTensorObj K L p q n h a) = a at ha
  change tensorDegreeProjection R K L p q n (ιTensorObj K L p q n h b) = b at hb
  exact ha.symm.trans ((congrArg (tensorDegreeProjection R K L p q n) hab).trans hb)

/-- 異なる第一次数に入る二つの元が等しければ、指定側の元は零。 -/
lemma tensorDegree_separation (p q i j n : ℤ) (h : p + q = n) (h' : i + j = n)
    (hi : i ≠ p) (a : (K.X p ⊗ L.X q : ModuleCat R)) (b : (K.X i ⊗ L.X j : ModuleCat R))
    (hab : ιTensorObj K L p q n h a = ιTensorObj K L i j n h' b) : a = 0 := by
  have ha := ConcreteCategory.congr_hom (tensorDegreeProjection_split R K L p q n h) a
  have hb := ConcreteCategory.congr_hom (tensorDegreeProjection_other R K L p q i j n h' hi) b
  change tensorDegreeProjection R K L p q n (ιTensorObj K L p q n h a) = a at ha
  change tensorDegreeProjection R K L p q n (ιTensorObj K L i j n h' b) = 0 at hb
  exact ha.symm.trans ((congrArg (tensorDegreeProjection R K L p q n) hab).trans hb)

/-- 係数 1 を読む線形汎関数を持つ元との tensor は、任意の加群で左消去できる。 -/
lemma tensor_left_cancel_of_coefficient
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (l : M →ₗ[R] R) (a : M) (ha : l a = 1) (b : N)
    (h : a ⊗ₜ[R] b = 0) : b = 0 := by
  have hh := congrArg (fun z => TensorProduct.lid R N
    (TensorProduct.map l (LinearMap.id : N →ₗ[R] N) z)) h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, ha,
    TensorProduct.lid_tmul, one_smul, map_zero] using hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
