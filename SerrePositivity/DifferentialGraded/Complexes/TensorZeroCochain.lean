module

public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# Complexes.TensorZeroCochain

## 概要
9 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## TensorEnriched（旧 SerrePositivity/DifferentialGraded/Complexes/TensorEnriched.lean） -/

/-! # 左 tensor の dg 豊穣関手

閉構造の転置を使い、非有界複体 K の左 tensor を全斉次 Hom に拡張する。
次数 p の射が K の次数 i と交換する Koszul 符号を成分上で検証する。
-/

@[expose] public section TensorEnriched
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorEnriched

/-! ## TensorRightHom（旧 SerrePositivity/DifferentialGraded/Complexes/TensorRightHom.lean） -/

/-! # 任意次数のcochainを右tensorする主Hom写像

signed symmetryによる共役で構成する。純tensor上では左因子だけに作用し、追加符号は消える。
-/

@[expose] public section TensorRightHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 全Homのchain mapは任意整数次数のcocycleをcocycleへ送る。 -/
lemma homComplexMap_closed {P Q R S : Complex A} (F : homComplex A P Q ⟶ homComplex A R S)
    (p : ℤ) (f : Cochain P Q p) (hf : δ p (p + 1) f = 0) :
    δ p (p + 1) (F.f p f) = 0 := by
  have h := ConcreteCategory.congr_hom (F.comm p (p + 1)) f
  change δ p (p + 1) (F.f p f) = F.f (p + 1) (δ p (p + 1) f) at h
  rw [hf, map_zero] at h
  exact h

/-- cochainの各斉次成分は整数単位スカラーを保つ。 -/
lemma cochain_v_units_smul {P Q : Complex A} {p : ℤ} (f : Cochain P Q p)
    (i n : ℤ) (hn : i + p = n) (a : ℤˣ) (x : P.X i) :
    f.v i n hn (a • x) = a • f.v i n hn x := by
  simp only [Units.smul_def, map_zsmul]

/-- 右tensorの全次数Hom写像。 -/
def tensorRightHom (K P Q : Complex A) :
    homComplex A P Q ⟶ homComplex A (P ⊗ K) (Q ⊗ K) :=
  tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    homPostcompose (P ⊗ K) (signedSwap K Q).hom

lemma tensorRightHom_cochain (K P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    (tensorRightHom K P Q).f p f =
      ((Cochain.ofHom (signedSwap P K).hom).comp ((tensorLeftHom K P Q).f p f)
        (zero_add p)).comp (Cochain.ofHom (signedSwap K Q).hom) (add_zero p) := rfl

/-- 純tensor上で、右tensorは追加のKoszul符号なしに左因子のcochainを適用する。 -/
lemma tensorRightHom_apply (K P Q : Complex A) (p i j a n : ℤ)
    (ha : i + j = a) (hn : a + p = n) (f : Cochain P Q p) (x : P.X i) (y : K.X j) :
    ((tensorRightHom K P Q).f p f).v a n hn
      (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    ιTensorObj Q K (i + p) j n (by omega) (f.v i (i + p) rfl x ⊗ₜ[A] y) := by
  rw [tensorRightHom_cochain, cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    signedSwap_apply, cochain_v_units_smul,
    tensorLeftHom_apply K P Q p j i a n (by omega) hn f y x,
    chain_units_smul, chain_units_smul, signedSwap_apply]
  simp only [smul_smul, ← Int.negOnePow_add]
  have he : i * j + (p * j + j * (i + p)) = 2 * (j * (i + p)) := by ring
  rw [he, Int.negOnePow_two_mul, one_smul]

end SerrePositivity.DifferentialGraded
end

end TensorRightHom

/-! ## TensorRightComposition（旧 SerrePositivity/DifferentialGraded/Complexes/TensorRightComposition.lean） -/

/-! # 右tensorの全次数合成と閉零chain mapとの整合性 -/

@[expose] public section TensorRightComposition
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorRightHom_apply_of_sum (K P Q : Complex A) (p i j a b n : ℤ)
    (ha : i + j = a) (hb : i + p = b) (hn : a + p = n)
    (f : Cochain P Q p) (x : P.X i) (y : K.X j) :
    ((tensorRightHom K P Q).f p f).v a n hn
      (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    ιTensorObj Q K b j n (by omega) (f.v i b hb x ⊗ₜ[A] y) := by
  subst b
  exact tensorRightHom_apply K P Q p i j a n ha hn f x y

lemma tensorRightHom_cochain_comp (K P Q T : Complex A) (p q m : ℤ) (hm : p + q = m)
    (f : Cochain P Q p) (g : Cochain Q T q) :
    (tensorRightHom K P T).f m (f.comp g hm) =
      ((tensorRightHom K P Q).f p f).comp ((tensorRightHom K Q T).f q g) hm := by
  apply Cochain.ext
  intro a n hn
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorRightHom K P T).f m (f.comp g hm)).v a n hn
    (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    (((tensorRightHom K P Q).f p f).comp
      ((tensorRightHom K Q T).f q g) hm).v a n hn
        (ιTensorObj P K i j a ha (x ⊗ₜ[A] y))
  rw [tensorRightHom_apply_of_sum K P T m i j a (i + p + q) n ha (by omega) hn,
    Cochain.comp_v _ _ hm i (i + p) (i + p + q) rfl rfl,
    Cochain.comp_v _ _ hm a (a + p) n rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [tensorRightHom_apply, tensorRightHom_apply]

lemma tensorRightHom_ofHom (K P Q : Complex A) (f : P ⟶ Q) :
    (tensorRightHom K P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (f ▷ K) := by
  apply Cochain.ext₀
  intro a
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorRightHom K P Q).f 0 (Cochain.ofHom f)).v a a (add_zero a)
    (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
      (f ▷ K).f a (ιTensorObj P K i j a ha (x ⊗ₜ[A] y))
  rw [tensorRightHom_apply_of_sum K P Q 0 i j a i a ha (add_zero i) (add_zero a),
    whiskerRight_apply, Cochain.ofHom_v]

end SerrePositivity.DifferentialGraded
end

end TensorRightComposition

/-! ## TensorGradedZero（旧 SerrePositivity/DifferentialGraded/Complexes/TensorGradedZero.lean） -/

/-! # chain条件を課さない次数0 cochainの右tensor

次数付き分裂を自由dg加群へ運ぶための成分API。
-/

@[expose] public section TensorGradedZero
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L T : Complex A}

def tensorGradedZeroComponent (r : Homogeneous K L 0) (P : Complex A) (n : ℤ) :
    (K ⊗ P).X n ⟶ (L ⊗ P).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij =>
    (r.v i i (add_zero i) ▷ P.X j) ≫ ιTensorObj L P i j n hij)

@[reassoc] lemma ι_tensorGradedZero (r : Homogeneous K L 0) (P : Complex A)
    (i j n : ℤ) (hij : i + j = n) :
    ιTensorObj K P i j n hij ≫ tensorGradedZeroComponent r P n =
      (r.v i i (add_zero i) ▷ P.X j) ≫ ιTensorObj L P i j n hij :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

lemma tensorGradedZeroComponent_ofHom (f : K ⟶ L) (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (Cochain.ofHom f) P n = (f ▷ P).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ι_tensorGradedZero, ι_whiskerRight, Cochain.ofHom_v]

lemma tensorGradedZeroComponent_add (r s : Homogeneous K L 0) (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (r + s) P n =
      tensorGradedZeroComponent r P n + tensorGradedZeroComponent s P n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [Preadditive.comp_add, ι_tensorGradedZero, Cochain.add_v,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

lemma tensorGradedZeroComponent_zero (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (0 : Homogeneous K L 0) P n = 0 := by
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [ι_tensorGradedZero, Cochain.zero_v,
    MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]

lemma tensorGradedZeroComponent_comp (r : Homogeneous K L 0) (s : Homogeneous L T 0)
    (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent r P n ≫ tensorGradedZeroComponent s P n =
      tensorGradedZeroComponent (r.comp s (zero_add 0)) P n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ι_tensorGradedZero_assoc, ι_tensorGradedZero]
  rw [ι_tensorGradedZero, Cochain.comp_zero_cochain_v]
  simp only [← Category.assoc, ← comp_whiskerRight]

lemma tensorGradedZeroComponent_id (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (Cochain.ofHom (𝟙 K)) P n = 𝟙 _ := by
  rw [tensorGradedZeroComponent_ofHom, id_whiskerRight, HomologicalComplex.id_f]

lemma tensorGradedZeroComponent_apply (r : Homogeneous K L 0) (P : Complex A)
    (i j n : ℤ) (hij : i + j = n) (x : K.X i) (y : P.X j) :
    tensorGradedZeroComponent r P n (ιTensorObj K P i j n hij (x ⊗ₜ[A] y)) =
      ιTensorObj L P i j n hij (r.v i i (add_zero i) x ⊗ₜ[A] y) :=
  congrArg (fun a => a (x ⊗ₜ[A] y)) (ι_tensorGradedZero r P i j n hij)

/-- 左tensor作用は因子の次数0 cochainと可換する。chain条件は不要。 -/
lemma tensorGradedZeroComponent_naturality (r : Homogeneous K L 0) {P Q : Complex A}
    (p i j : ℤ) (hij : i + p = j) (a : Homogeneous P Q p) :
    ((tensorLeftHom K P Q).f p a).v i j hij ≫ tensorGradedZeroComponent r Q j =
      tensorGradedZeroComponent r P i ≫ ((tensorLeftHom L P Q).f p a).v i j hij := by
  apply mapBifunctor.hom_ext
  intro b c hbc
  change b + c = i at hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change tensorGradedZeroComponent r Q j
    (((tensorLeftHom K P Q).f p a).v i j hij (ιTensorObj K P b c i hbc (x ⊗ₜ[A] y))) =
    ((tensorLeftHom L P Q).f p a).v i j hij
      (tensorGradedZeroComponent r P i (ιTensorObj K P b c i hbc (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply, tensorGradedZeroComponent_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorGradedZeroComponent_apply, tensorLeftHom_apply]
  rfl

end SerrePositivity.DifferentialGraded
end

end TensorGradedZero

/-! ## TensorCochainInterchange（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCochainInterchange.lean） -/

/-! # 全次数cochainの左右tensorの交差符号

異なる二つのtensor因子に作用するcochainの順序交換は、次数積のKoszul符号を持つ。
ε消去と後方のcochainの交換にも使用する。
-/

@[expose] public section TensorCochainInterchange
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左因子と右因子へのcochain作用を交換する際の符号は(-1)^(pq)。 -/
lemma tensorCochain_interchange (P P' Q Q' : Complex A) (p q m : ℤ)
    (hm : p + q = m) (hm' : q + p = m) (f : Cochain P P' p) (g : Cochain Q Q' q) :
    ((tensorRightHom Q P P').f p f).comp ((tensorLeftHom P' Q Q').f q g) hm =
      (p * q).negOnePow • (((tensorLeftHom P Q Q').f q g).comp
        ((tensorRightHom Q' P P').f p f) hm') := by
  apply Cochain.ext
  intro a n hn
  rw [Units.smul_def, Cochain.smul_v]
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rw [Cochain.comp_v _ _ hm a (a + p) n rfl (by omega)]
  change ((tensorLeftHom P' Q Q').f q g).v (a + p) n (by omega)
    (((tensorRightHom Q P P').f p f).v a (a + p) rfl
      (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y))) =
    (p * q).negOnePow •
      ((((tensorLeftHom P Q Q').f q g).comp
        ((tensorRightHom Q' P P').f p f) hm').v a n hn
          (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y)))
  rw [tensorRightHom_apply,
    tensorLeftHom_apply_of_sum P' Q Q' q (i + p) j (a + p) (j + q) n
      (by omega) rfl (by omega)]
  rw [Cochain.comp_v _ _ hm' a (a + q) n rfl (by omega)]
  change (q * (i + p)).negOnePow •
      ιTensorObj P' Q' (i + p) (j + q) n (by omega)
        (f.v i (i + p) rfl x ⊗ₜ[A] g.v j (j + q) rfl y) =
    (p * q).negOnePow • ((tensorRightHom Q' P P').f p f).v (a + q) n (by omega)
      (((tensorLeftHom P Q Q').f q g).v a (a + q) rfl
        (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply_of_sum P Q Q' q i j a (j + q) (a + q) ha rfl rfl,
    cochain_v_units_smul, tensorRightHom_apply, smul_smul, ← Int.negOnePow_add]
  congr 2
  ring

/-- 次数1同士の異なる因子への作用は反交換する。 -/
lemma tensorCochain_odd_anticommute (P P' Q Q' : Complex A)
    (f : Cochain P P' 1) (g : Cochain Q Q' 1) :
    ((tensorRightHom Q P P').f 1 f).comp ((tensorLeftHom P' Q Q').f 1 g)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom P Q Q').f 1 g).comp ((tensorRightHom Q' P P').f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega)) := by
  simpa [Units.smul_def] using
    tensorCochain_interchange P P' Q Q' 1 1 2 (by omega) (by omega) f g

end SerrePositivity.DifferentialGraded
end

end TensorCochainInterchange

/-! ## TensorCochainComposition（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCochainComposition.lean） -/

/-! # 左tensorによる全次数cochain合成の保存

豊穣合成の保存から通常順の斉次合成の保存を取り出す。
主モデルの豊穣合成に付く共通Koszul符号を単位スカラーの作用の単射性で消す。
-/

@[expose] public section TensorCochainComposition
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左tensorの全Hom写像は通常順のcochain合成も保存する。 -/
lemma tensorLeftHom_cochain_comp (K P Q T : Complex A) (p q m : ℤ) (hm : p + q = m)
    (f : Cochain P Q p) (g : Cochain Q T q) :
    (tensorLeftHom K P T).f m (f.comp g hm) =
      ((tensorLeftHom K P Q).f p f).comp ((tensorLeftHom K Q T).f q g) hm := by
  have h := congrArg (fun t : homComplex A P Q ⊗ homComplex A Q T ⟶
      homComplex A (K ⊗ P) (K ⊗ T) =>
    t.f m (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g)))
    (tensorLeftHom_comp K P Q T)
  change (tensorLeftHom K P T).f m
    ((enrichedComposition P Q T).f m
      (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f m
      ((tensorLeftHom K P Q ⊗ₘ tensorLeftHom K Q T).f m
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply] at h
  simp only [Units.smul_def, map_zsmul] at h
  exact smul_left_cancel (p * q).negOnePow h

/-- 左tensorは二つのcochainの符号付き反交換式を保つ。 -/
lemma tensorLeftHom_cochain_anticommute (K P Q Q' T : Complex A)
    (p q m : ℤ) (hm : p + q = m) (hm' : q + p = m)
    (f : Cochain P Q p) (g : Cochain Q T q)
    (g' : Cochain P Q' q) (f' : Cochain Q' T p)
    (h : f.comp g hm = -(g'.comp f' hm')) :
    ((tensorLeftHom K P Q).f p f).comp ((tensorLeftHom K Q T).f q g) hm =
      -(((tensorLeftHom K P Q').f q g').comp ((tensorLeftHom K Q' T).f p f') hm') := by
  rw [← tensorLeftHom_cochain_comp, h, map_neg, tensorLeftHom_cochain_comp]

end SerrePositivity.DifferentialGraded
end

end TensorCochainComposition

/-! ## TensorClosedZero（旧 SerrePositivity/DifferentialGraded/Complexes/TensorClosedZero.lean） -/

/-! # 全次数tensor写像の閉零chain mapとの一致 -/

@[expose] public section TensorClosedZero
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左tensorの全Hom写像は通常のchain mapのwhiskerLeftと一致する。 -/
lemma tensorLeftHom_ofHom (K P Q : Complex A) (f : P ⟶ Q) :
    (tensorLeftHom K P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (K ◁ f) := by
  apply Cochain.ext₀
  intro a
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorLeftHom K P Q).f 0 (Cochain.ofHom f)).v a a (add_zero a)
    (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) =
      (K ◁ f).f a (ιTensorObj K P i j a ha (x ⊗ₜ[A] y))
  rw [tensorLeftHom_apply_of_sum K P Q 0 i j a j a ha (add_zero j) (add_zero a),
    whiskerLeft_apply]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

end SerrePositivity.DifferentialGraded
end

end TensorClosedZero

/-! ## TensorZeroCochain（旧 SerrePositivity/DifferentialGraded/Complexes/TensorZeroCochain.lean） -/

/-! # 閉性を仮定しない二つの次数0 cochainのtensor -/

@[expose] public section TensorZeroCochain
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma homComplexMap_differential {P Q R T : Complex A}
    (F : homComplex A P Q ⟶ homComplex A R T) (p q : ℤ) (f : Cochain P Q p) :
    δ p q (F.f p f) = F.f q (δ p q f) :=
  ConcreteCategory.congr_hom (F.comm p q) f

/-- 二つの次数0 cochainのtensor。どちらの閉性も必要としない。 -/
def tensorZeroCochain {P P' Q Q' : Complex A} (f : Cochain P P' 0) (g : Cochain Q Q' 0) :
    Cochain (P ⊗ Q) (P' ⊗ Q') 0 :=
  ((tensorRightHom Q P P').f 0 f).comp ((tensorLeftHom P' Q Q').f 0 g) (zero_add 0)

lemma tensorZeroCochain_ofHom {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorZeroCochain (Cochain.ofHom f) (Cochain.ofHom g) = Cochain.ofHom (f ⊗ₘ g) := by
  rw [tensorZeroCochain, tensorRightHom_ofHom, tensorLeftHom_ofHom,
    ← Cochain.ofHom_comp, ← tensorHom_def]

lemma tensorZeroCochain_apply {P P' Q Q' : Complex A} (f : Cochain P P' 0) (g : Cochain Q Q' 0)
    (i j n : ℤ) (hn : i + j = n) (x : P.X i) (y : Q.X j) :
    (tensorZeroCochain f g).v n n (add_zero n)
      (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
    ιTensorObj P' Q' i j n hn
      (f.v i i (add_zero i) x ⊗ₜ[A] g.v j j (add_zero j) y) := by
  rw [tensorZeroCochain, Cochain.comp_zero_cochain_v]
  change ((tensorLeftHom P' Q Q').f 0 g).v n n (add_zero n)
    (((tensorRightHom Q P P').f 0 f).v n n (add_zero n)
      (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y))) = _
  rw [tensorRightHom_apply_of_sum Q P P' 0 i j n i n hn (add_zero i) (add_zero n),
    tensorLeftHom_apply_of_sum P' Q Q' 0 i j n j n hn (add_zero j) (add_zero n)]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]

lemma tensorZeroCochain_differential {P P' Q Q' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) :
    δ 0 1 (tensorZeroCochain f g) =
    ((tensorRightHom Q P P').f 0 f).comp
      ((tensorLeftHom P' Q Q').f 1 (δ 0 1 g)) (zero_add 1) +
    ((tensorRightHom Q P P').f 1 (δ 0 1 f)).comp
      ((tensorLeftHom P' Q Q').f 0 g) (add_zero 1) := by
  rw [tensorZeroCochain, δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1)]
  rw [homComplexMap_differential (tensorLeftHom P' Q Q') 0 1 g,
    homComplexMap_differential (tensorRightHom Q P P') 0 1 f]
  simp only [Int.negOnePow_zero, one_smul]

end SerrePositivity.DifferentialGraded
end

end TensorZeroCochain

/-! ## TensorZeroCochainNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/TensorZeroCochainNaturality.lean） -/

/-! # 閉零の左写像を持つcochain tensorの右前合成自然性 -/

@[expose] public section TensorZeroCochainNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_precomp_right {P P' Q R T : Complex A}
    (F : P ⟶ P') (c : Q ⟶ R) (g : Cochain R T 0) :
    (Cochain.ofHom (P ◁ c)).comp (tensorZeroCochain (Cochain.ofHom F) g) (zero_add 0) =
    tensorZeroCochain (Cochain.ofHom F) ((Cochain.ofHom c).comp g (zero_add 0)) := by
  apply Cochain.ext₀
  intro n
  apply mapBifunctor.hom_ext
  intro i j hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((Cochain.ofHom (P ◁ c)).comp (tensorZeroCochain (Cochain.ofHom F) g)
      (zero_add 0)).v n n (add_zero n) (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
    (tensorZeroCochain (Cochain.ofHom F) ((Cochain.ofHom c).comp g (zero_add 0))).v n n
      (add_zero n) (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y))
  rw [cochain_ofHom_comp_apply, whiskerLeft_apply, tensorZeroCochain_apply,
    tensorZeroCochain_apply, cochain_ofHom_comp_apply]

end SerrePositivity.DifferentialGraded
end

end TensorZeroCochainNaturality
