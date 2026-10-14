module
public import SerrePositivity.DifferentialGraded.Complexes.Enrichment
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 左 tensor の dg 豊穣関手

閉構造の転置を使い、非有界複体 K の左 tensor を全斉次 Hom に拡張する。
次数 p の射が K の次数 i と交換する Koszul 符号を成分上で検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 全次数 Hom 上の左 tensor の chain map。 -/
def tensorLeftHom (K P Q : Complex A) :
    homComplex A P Q ⟶ homComplex A (K ⊗ P) (K ⊗ Q) :=
  tensorHomEquiv (K ⊗ P) (homComplex A P Q) (K ⊗ Q)
    ((α_ K P (homComplex A P Q)).hom ≫ K ◁ evaluation P Q)

/-- 左 tensor の斉次射は K の次数 i に対して (-1)^(pi) を持つ。 -/
lemma tensorLeftHom_apply (K P Q : Complex A) (p i j a n : ℤ)
    (ha : i + j = a) (hn : a + p = n) (f : Homogeneous P Q p)
    (x : K.X i) (y : P.X j) :
    ((tensorLeftHom K P Q).f p f).v a n hn
      (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) =
    (p * i).negOnePow • ιTensorObj K Q i (j + p) n (by omega)
      (x ⊗ₜ[A] f.v j (j + p) rfl y) := by
  rw [tensorLeftHom, tensorHomEquiv_component]
  change (p * a).negOnePow • (K ◁ evaluation P Q).f n
    ((α_ K P (homComplex A P Q)).hom.f n
      (ιTensorObj (K ⊗ P) (homComplex A P Q) a p n hn
        (ιTensorObj K P i j a ha (x ⊗ₜ[A] y) ⊗ₜ[A] f))) = _
  rw [associator_apply_of_sum, whiskerLeft_apply, evaluation_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  change ((p * a).negOnePow * (j * p).negOnePow) • (_ : (K ⊗ Q).X n) =
    (p * i).negOnePow • (_ : (K ⊗ Q).X n)
  rw [← Int.negOnePow_add]
  have he : p * a + j * p = p * i + 2 * (p * j) := by rw [← ha]; ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 出力の第二因子の次数を指定した左 tensor の成分公式。 -/
lemma tensorLeftHom_apply_of_sum (K P Q : Complex A) (p i j a b n : ℤ)
    (ha : i + j = a) (hb : j + p = b) (hn : a + p = n) (f : Homogeneous P Q p)
    (x : K.X i) (y : P.X j) :
    ((tensorLeftHom K P Q).f p f).v a n hn
      (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) =
    (p * i).negOnePow • ιTensorObj K Q i b n (by omega)
      (x ⊗ₜ[A] f.v j b hb y) := by
  subst b
  exact tensorLeftHom_apply K P Q p i j a n ha hn f x y

/-- 左 tensor の全次数 Hom 射は閉単位を保存する。 -/
lemma tensorLeftHom_id (K P : Complex A) :
    identity P ≫ tensorLeftHom K P P = identity (K ⊗ P) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (identity P ≫ tensorLeftHom K P P)).val =
    (cycleFromUnit _ (identity (K ⊗ P))).val
  rw [cycleFromUnit_postcomp, identity, identity, cycleFromUnit_unitFromCycle,
    cycleFromUnit_unitFromCycle]
  change (tensorLeftHom K P P).f 0 (Cochain.ofHom (𝟙 P)) =
    Cochain.ofHom (𝟙 (K ⊗ P))
  apply Cochain.ext₀
  intro a
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorLeftHom K P P).f 0 (Cochain.ofHom (𝟙 P))).v a a (add_zero a)
    (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) = _
  rw [tensorLeftHom_apply_of_sum K P P 0 i j a j a ha (add_zero j) (add_zero a)]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  simp
  rfl
/-- 左 tensor の全次数 Hom 射は豊穣合成を保存する。 -/
lemma tensorLeftHom_comp (K P Q T : Complex A) :
    enrichedComposition P Q T ≫ tensorLeftHom K P T =
    (tensorLeftHom K P Q ⊗ₘ tensorLeftHom K Q T) ≫
      enrichedComposition (K ⊗ P) (K ⊗ Q) (K ⊗ T) := by
  apply tensorHom_ext
  intro p q m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (tensorLeftHom K P T).f m
    ((enrichedComposition P Q T).f m
      (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f m
      ((tensorLeftHom K P Q ⊗ₘ tensorLeftHom K Q T).f m
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • (tensorLeftHom K P T).f m (f.comp g hm) =
    (p * q).negOnePow • (((tensorLeftHom K P Q).f p f).comp
      ((tensorLeftHom K Q T).f q g) hm)
  apply congrArg ((p * q).negOnePow • ·)
  apply Cochain.ext
  intro a n hn
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorLeftHom K P T).f m (f.comp g hm)).v a n hn
    (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) = _
  rw [tensorLeftHom_apply_of_sum K P T m i j a (j + p + q) n ha (by omega) hn,
    Cochain.comp_v _ _ hm j (j + p) (j + p + q) rfl rfl,
    Cochain.comp_v _ _ hm a (a + p) n rfl (by omega)]
  change (m * i).negOnePow • ιTensorObj K T i (j + p + q) n (by omega)
      (x ⊗ₜ[A] g.v (j + p) (j + p + q) rfl (f.v j (j + p) rfl y)) =
    ((tensorLeftHom K Q T).f q g).v (a + p) n (by omega)
      (((tensorLeftHom K P Q).f p f).v a (a + p) rfl
        (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorLeftHom_apply_of_sum K Q T q i (j + p) (a + p) (j + p + q) n
    (by omega) rfl (by omega)]
  change (m * i).negOnePow • (_ : (K ⊗ T).X n) =
    (p * i).negOnePow • (q * i).negOnePow • (_ : (K ⊗ T).X n)
  rw [smul_smul, ← Int.negOnePow_add]
  congr 2
  rw [← hm]
  ring

/-- 任意非有界 K の左 tensor は Ch(A) の dg 関手。 -/
def tensorLeftDG (K : Complex A) : DGFunctor A (Complex A) (Complex A) where
  obj P := K ⊗ P
  map P Q := tensorLeftHom K P Q
  map_id := tensorLeftHom_id K
  map_comp := tensorLeftHom_comp K
/-- 左 tensor の Hom 作用は左因子の chain map で自然。 -/
lemma tensorLeftHom_naturality {K L : Complex A} (g : K ⟶ L) (P Q : Complex A) :
    tensorLeftHom K P Q ≫ homPostcompose (K ⊗ P) (g ⊗ₘ 𝟙 Q) =
    tensorLeftHom L P Q ≫ homPrecompose (g ⊗ₘ 𝟙 P) (L ⊗ Q) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((tensorLeftHom K P Q).f p f).comp (Cochain.ofHom (g ⊗ₘ 𝟙 Q))
    (add_zero p)) =
    (Cochain.ofHom (g ⊗ₘ 𝟙 P)).comp ((tensorLeftHom L P Q).f p f) (zero_add p)
  apply Cochain.ext
  intro a n hn
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  change (g ⊗ₘ 𝟙 Q).f n (((tensorLeftHom K P Q).f p f).v a n hn
      (ιTensorObj K P i j a ha (x ⊗ₜ[A] y))) =
    ((tensorLeftHom L P Q).f p f).v a n hn
      ((g ⊗ₘ 𝟙 P).f a (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply, tensorMap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorMap_apply, tensorLeftHom_apply]
  rfl
end SerrePositivity.DifferentialGraded
