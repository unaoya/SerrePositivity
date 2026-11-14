module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
public import SerrePositivity.HomologicalAlgebra.BicomplexProjection
import Mathlib.Algebra.Category.ModuleCat.Colimits
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential
import Mathlib.Algebra.TrivSqZeroExt.Basic
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# pd 座標写像の連鎖律

## 概要
pd Čech 模型の頂点写像と、その線形な微分座標変換を偏微分で照合する。

## 方針
平方零拡大を使い、連鎖律を第 0 頂点と分冪差座標の生成元で確認する。

## 規約
座標変換の行列は、第 0 頂点と差座標の基底で書く。

## 使われ方
pd de Rham 列微分の余単体的自然性。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private def coordinateChange {m n : SimplexCategory} (θ : m ⟶ n) :
    (pdCoordinates r m.len →₀ k) →ₗ[k] pdCoordinates r n.len →₀ k :=
  (copyToCoordinate k r n).comp ((copyModuleMap k r θ).comp (coordinateToCopy k r m))

private def coordinateEntry {m n : SimplexCategory} (θ : m ⟶ n)
    (a : pdCoordinates r m.len) (b : pdCoordinates r n.len) : k :=
  coordinateChange k r θ (Finsupp.single a 1) b

@[local simp] private theorem copyToCoordinate_vertex (n : SimplexCategory)
    (j : Fin r) (i : Fin (n.len + 1)) :
    copyToCoordinate k r n (Finsupp.single (j,i) 1) =
      Finsupp.single (.inl j) 1 + Finsupp.embDomain Function.Embedding.inr (vertexDiff k r n j i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [copyToCoordinate, Finsupp.linearCombination_single, vertexDiff]
  · simp [copyToCoordinate, Finsupp.linearCombination_single, vertexDiff]

private theorem copyModuleMap_single {m n : SimplexCategory} (θ : m ⟶ n)
    (j : Fin r) (i : Fin (m.len+1)) :
    copyModuleMap k r θ (Finsupp.single (j,i) 1) = Finsupp.single (j, θ.toOrderHom i) 1 :=
  Finsupp.mapDomain_single

private theorem coordinateChange_left {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin r) :
    coordinateChange k r θ (Finsupp.single (.inl j) 1) =
      Finsupp.single (.inl j) 1 +
        Finsupp.embDomain Function.Embedding.inr (vertexDiff k r n j (θ.toOrderHom 0)) := by
  change copyToCoordinate k r n
    (copyModuleMap k r θ (coordinateToCopy k r m (Finsupp.single (.inl j) 1))) = _
  rw [coordinateToCopy_single]
  change copyToCoordinate k r n (copyModuleMap k r θ (Finsupp.single (j,0) 1)) = _
  rw [copyModuleMap_single, copyToCoordinate_vertex]

private theorem coordinateChange_right {m n : SimplexCategory} (θ : m ⟶ n) (x : Diff k r m) :
    coordinateChange k r θ (Finsupp.embDomain Function.Embedding.inr x) =
      Finsupp.embDomain Function.Embedding.inr (diffMap k r θ x) := by
  let iM : Diff k r m →ₗ[k] (pdCoordinates r m.len →₀ k) :=
    Finsupp.lmapDomain k k Sum.inr
  let iN : Diff k r n →ₗ[k] (pdCoordinates r n.len →₀ k) :=
    Finsupp.lmapDomain k k Sum.inr
  have hiM (x : Diff k r m) : iM x = Finsupp.embDomain Function.Embedding.inr x :=
    (Finsupp.embDomain_eq_mapDomain Function.Embedding.inr x).symm
  have hiN (x : Diff k r n) : iN x = Finsupp.embDomain Function.Embedding.inr x :=
    (Finsupp.embDomain_eq_mapDomain Function.Embedding.inr x).symm
  suffices h : (coordinateChange k r θ).comp iM = iN.comp (diffMap k r θ) by
    have he := DFunLike.congr_fun h x
    change coordinateChange k r θ (iM x) = iN (diffMap k r θ x) at he
    rwa [hiM, hiN] at he
  apply (Finsupp.basisSingleOne (R := k)).ext
  rintro ⟨j,i⟩
  change coordinateChange k r θ (iM (Finsupp.single (j,i) 1)) =
    iN (diffMap k r θ (Finsupp.single (j,i) 1))
  rw [hiM, hiN, Finsupp.embDomain_single]
  change copyToCoordinate k r n
    (copyModuleMap k r θ (coordinateToCopy k r m (Finsupp.single (.inr (j,i)) 1))) = _
  rw [coordinateToCopy_single]
  change copyToCoordinate k r n
    (copyModuleMap k r θ (Finsupp.single (j,i.succ) 1 - Finsupp.single (j,0) 1)) = _
  rw [map_sub, copyModuleMap_single, copyModuleMap_single, map_sub,
    copyToCoordinate_vertex, copyToCoordinate_vertex, add_sub_add_left_eq_sub]
  change _ = Finsupp.embDomain Function.Embedding.inr (diffMap k r θ (vertexDiff k r m j i.succ))
  rw [diffMap_vertex]
  simp only [← hiN, map_sub]

private theorem coordinateChange_sum {m n : SimplexCategory} (θ : m ⟶ n)
    (x : pdCoordinates r m.len →₀ k) (b : pdCoordinates r n.len) :
    coordinateChange k r θ x b = ∑ a, x a * coordinateEntry k r θ a b := by
  classical
  let F := (Finsupp.lapply b).comp (coordinateChange k r θ)
  let G : (pdCoordinates r m.len →₀ k) →ₗ[k] k :=
    ∑ a, (coordinateEntry k r θ a b) • Finsupp.lapply a
  have h : F = G := by
    apply (Finsupp.basisSingleOne (R := k)).ext
    intro a
    change coordinateEntry k r θ a b = G (Finsupp.single a 1)
    simp only [G, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hx := DFunLike.congr_fun h x
  change coordinateChange k r θ x b = G x at hx
  simpa only [G, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul,
    mul_comm] using hx

section Relative

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private def relativeDerivationJet (f : A →ₐ[k] B) (d : A →ₗ[k] B)
    (h : ∀ x y, d (x * y) = f x * d y + f y * d x) :
    A →ₐ[k] TrivSqZeroExt B B where
  toFun x := (f x, d x)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero d)
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    have e := h 1 1
    simp only [mul_one, map_one, one_mul] at e
    change d 1 = 0
    exact add_left_cancel (show d 1 + d 1 = d 1 + 0 by rw [add_zero]; exact e.symm))
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' x y := TrivSqZeroExt.ext (map_mul _ _ _) (by
    change d (x*y) = f x • d y + MulOpposite.op (f y) • d x
    rw [op_smul_eq_smul]
    exact h x y)
  commutes' c := TrivSqZeroExt.ext (f.commutes c) (by
    have e := h 1 1
    simp only [mul_one, map_one, one_mul] at e
    have h₁ : d 1 = 0 := add_left_cancel (show d 1 + d 1 = d 1 + 0 by rw [add_zero]; exact e.symm)
    change d (algebraMap k A c) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h₁, smul_zero])

end Relative

private def chainLhs {m n : SimplexCategory} (θ : m ⟶ n) (b : pdCoordinates r n.len) :
    pdRaw k r m.len →ₗ[k] pdRaw k r n.len :=
  (pdRawDerivation k r n.len b).toLinearMap.comp (pdRawMap k r θ).toLinearMap

private def chainRhs {m n : SimplexCategory} (θ : m ⟶ n) (b : pdCoordinates r n.len) :
    pdRaw k r m.len →ₗ[k] pdRaw k r n.len :=
  ∑ a, coordinateEntry k r θ a b •
    ((pdRawMap k r θ).toLinearMap.comp (pdRawDerivation k r m.len a).toLinearMap)

private theorem chainLhs_leibniz {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (x y : pdRaw k r m.len) :
    chainLhs k r θ b (x*y) =
      pdRawMap k r θ x * chainLhs k r θ b y + pdRawMap k r θ y * chainLhs k r θ b x := by
  change pdRawDerivation k r n.len b (pdRawMap k r θ (x*y)) = _
  rw [map_mul, Derivation.leibniz]
  rfl

private theorem chainRhs_leibniz {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (x y : pdRaw k r m.len) :
    chainRhs k r θ b (x*y) =
      pdRawMap k r θ x * chainRhs k r θ b y + pdRawMap k r θ y * chainRhs k r θ b x := by
  simp only [chainRhs, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, smul_add, Finset.mul_sum, ← Finset.sum_add_distrib, Algebra.mul_smul_comm]

private theorem chainRule_of_generators {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len)
    (hX : ∀ j, chainLhs k r θ b (baseVar k r m j) = chainRhs k r θ b (baseVar k r m j))
    (hDP : ∀ q x, chainLhs k r θ b (includeRight (DividedPowerAlgebra.dp k q x)) =
      chainRhs k r θ b (includeRight (DividedPowerAlgebra.dp k q x))) :
    chainLhs k r θ b = chainRhs k r θ b := by
  let f := pdRawMap k r θ
  let L := relativeDerivationJet k f (chainLhs k r θ b) (chainLhs_leibniz k r θ b)
  let R := relativeDerivationJet k f (chainRhs k r θ b) (chainRhs_leibniz k r θ b)
  have h : L = R := by
    apply Algebra.TensorProduct.ext
    · apply MvPolynomial.algHom_ext
      intro j
      exact TrivSqZeroExt.ext rfl (hX j)
    · apply DividedPowerAlgebra.algHom_ext
      intro q x
      exact TrivSqZeroExt.ext rfl (hDP q x)
  exact LinearMap.ext fun x => congrArg (fun g : _ →ₐ[k] TrivSqZeroExt _ _ => (g x).snd) h

private abbrev dpCoordinate {n : SimplexCategory} (q : ℕ) (x : Diff k r n) : pdRaw k r n.len :=
  includeRight (DividedPowerAlgebra.dp k q x)

private theorem baseVar_partial (n : SimplexCategory) (j : Fin r) (a : pdCoordinates r n.len) :
    pdRawPartial k r n.len a (baseVar k r n j) =
      algebraMap k _ (Finsupp.single (.inl j) (1 : k) a) := by
  rcases a with a | a
  · change pdRawPartial k r n.len (.inl a) (MvPolynomial.X j ⊗ₜ[k] 1) = _
    rw [partial_inl_tmul]
    change (MvPolynomial.pderiv a (MvPolynomial.X j : MvPolynomial (Fin r) k)) ⊗ₜ[k] 1 = _
    rw [MvPolynomial.pderiv_X, Pi.single_apply, Finsupp.single_apply]
    by_cases h : j = a
    · subst a
      simp
    · simp [h]
  · change pdRawPartial k r n.len (.inr a) (MvPolynomial.X j ⊗ₜ[k] 1) = _
    rw [partial_inr_tmul, Derivation.map_one_eq_zero, TensorProduct.tmul_zero]
    simp

private theorem dpCoordinate_partial {n : SimplexCategory} (q : ℕ) (x : Diff k r n)
    (a : pdCoordinates r n.len) :
    pdRawPartial k r n.len a (dpCoordinate k r (q+1) x) =
      (Finsupp.embDomain Function.Embedding.inr x a) • dpCoordinate k r q x := by
  rcases a with a | a
  · change pdRawPartial k r n.len (.inl a)
      ((1 : MvPolynomial (Fin r) k) ⊗ₜ[k] DividedPowerAlgebra.dp k (q+1) x) = _
    rw [partial_inl_tmul, Derivation.map_one_eq_zero, TensorProduct.zero_tmul]
    have h : Sum.inl a ∉ Set.range (Function.Embedding.inr :
        (Fin r × Fin n.len) ↪ pdCoordinates r n.len) := by simp
    rw [Finsupp.embDomain_of_notMem_range _ _ _ h, zero_smul]
  · have h := Finsupp.embDomain_apply_self (Function.Embedding.inr :
      (Fin r × Fin n.len) ↪ pdCoordinates r n.len) x a
    rw [show Finsupp.embDomain Function.Embedding.inr x (.inr a) = x a from h]
    exact pdRawPartial_dp_succ k r n.len a q x

private theorem copy_partial (n : SimplexCategory) (j : Fin r) (i : Fin (n.len+1))
    (a : pdCoordinates r n.len) :
    pdRawPartial k r n.len a (copy k r n j i) =
      algebraMap k _ (copyToCoordinate k r n (Finsupp.single (j,i) 1) a) := by
  change pdRawPartial k r n.len a (baseVar k r n j +
    dpCoordinate k r 1 (vertexDiff k r n j i)) = _
  rw [map_add, baseVar_partial, dpCoordinate_partial k r 0, copyToCoordinate_vertex]
  simp [dpCoordinate, DividedPowerAlgebra.dp_zero, Algebra.smul_def, map_add]

private theorem chainRule_baseVar {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (j : Fin r) :
    chainLhs k r θ b (baseVar k r m j) = chainRhs k r θ b (baseVar k r m j) := by
  simp only [chainLhs, chainRhs, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    pdRawDerivation_toLinearMap, AlgHom.toLinearMap_apply, baseVar_partial, AlgHom.commutes]
  rw [pdRawMap_baseVar, copy_partial, copyToCoordinate_vertex, ← coordinateChange_left]
  change algebraMap k _ (coordinateEntry k r θ (.inl j) b) = _
  classical
  simp [Finsupp.single_apply, Algebra.smul_def, apply_ite]

private theorem chainRule_dp {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (q : ℕ) (x : Diff k r m) :
    chainLhs k r θ b (dpCoordinate k r q x) = chainRhs k r θ b (dpCoordinate k r q x) := by
  have h (q' : ℕ) : pdRawMap k r θ (dpCoordinate k r q' x) =
      dpCoordinate k r q' (diffMap k r θ x) := by
    have e := DFunLike.congr_fun (pdRawMap_right k r θ) (DividedPowerAlgebra.dp k q' x)
    simpa only [AlgHom.comp_apply, DividedPowerAlgebra.map_apply_dp] using e
  cases q with
  | zero =>
    have e : dpCoordinate k r 0 x = 1 := by
      rw [dpCoordinate, DividedPowerAlgebra.dp_zero, map_one]
    rw [e]
    simp [chainLhs, chainRhs]
  | succ q =>
    simp only [chainLhs, chainRhs, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      pdRawDerivation_toLinearMap, AlgHom.toLinearMap_apply, h, dpCoordinate_partial, map_smul]
    rw [← coordinateChange_right k r θ, coordinateChange_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a _
    rw [smul_smul, mul_comm]

/-- 余単体の構造射に対する pd 偏微分の連鎖律。 -/
private theorem pdRawPartial_chainRule {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (x : pdRaw k r m.len) :
    pdRawPartial k r n.len b (pdRawMap k r θ x) =
      ∑ a, coordinateEntry k r θ a b • pdRawMap k r θ (pdRawPartial k r m.len a x) := by
  have h := chainRule_of_generators k r θ b (chainRule_baseVar k r θ b) (chainRule_dp k r θ b)
  simpa only [chainLhs, chainRhs, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    pdRawDerivation_toLinearMap, AlgHom.toLinearMap_apply] using DFunLike.congr_fun h x

open SerrePositivity.DerivedCompletion

private theorem pdTermMap_unit {m n : SimplexCategory} (θ : m ⟶ n) (x : pdRaw k r m.len) :
    pdTermMap p k r θ (principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r m.len)) x) =
      principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n.len)) (pdRawMap k r θ x) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p (rawTermMap k r θ)) x

private theorem pdPartial_chainRule {m n : SimplexCategory} (θ : m ⟶ n)
    (b : pdCoordinates r n.len) (x : pdTerm p k r m.len) :
    pdPartial p k r n.len b (pdTermMap p k r θ x) =
      ∑ a, coordinateEntry k r θ a b • pdTermMap p k r θ (pdPartial p k r m.len a x) := by
  let F := (pdPartial p k r n.len b).comp (pdTermMap p k r θ)
  let G : pdTerm p k r m.len →ₗ[k] pdTerm p k r n.len :=
    ∑ a, coordinateEntry k r θ a b • (pdTermMap p k r θ).comp (pdPartial p k r m.len a)
  have h : F = G := by
    apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
    intro y
    let U := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n.len))
    let V := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r m.len))
    let u : pdRaw k r n.len →ₗ[k] pdTerm p k r n.len :=
      { toFun := U.hom
        map_add' := U.hom.map_add
        map_smul' := fun c z => by
          change U.hom (c • z) = c • U.hom z
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          rfl }
    change F (V y) = G (V y)
    have hF : F (V y) = u (pdRawPartial k r n.len b (pdRawMap k r θ y)) := by
      change pdPartial p k r n.len b (pdTermMap p k r θ (V y)) = _
      rw [show pdTermMap p k r θ (V y) = U (pdRawMap k r θ y) from pdTermMap_unit p k r θ y]
      exact principalCompletionLinearMap_unit k p (pdRawPartial k r n.len b) _
    rw [hF, pdRawPartial_chainRule, map_sum]
    simp only [G, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    rw [show pdPartial p k r m.len a (V y) = V (pdRawPartial k r m.len a y) from
      principalCompletionLinearMap_unit k p (pdRawPartial k r m.len a) y]
    exact (pdTermMap_unit p k r θ _).symm
  simpa only [F, G, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] using
    DFunLike.congr_fun h x

private theorem wedgeOne_map {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (f : M →ₗ[k] N) (j : ℕ)
    (a : ⋀[k]^1 M) (x : ⋀[k]^j M) :
    exteriorPower.map (j+1) f (DeRham.wedgeOne k M j a x) =
      DeRham.wedgeOne k N j (exteriorPower.map 1 f a) (exteriorPower.map j f x) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, DeRham.wedgeOne_coe, map_mul]

private theorem exteriorPower_map_one {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (f : M →ₗ[k] N) (v : M) :
    exteriorPower.map 1 f ((exteriorPower.oneEquiv k M).symm v) =
      (exteriorPower.oneEquiv k N).symm (f v) := by
  simp [exteriorPower.oneEquiv_symm_apply, Function.comp_def]

private theorem coordinateVector_sum {m n : SimplexCategory} (θ : m ⟶ n)
    (a : pdCoordinates r m.len) :
    copyModuleMap k r θ (pdCoordinateVector k r m a) =
      ∑ b, coordinateEntry k r θ a b • pdCoordinateVector k r n b := by
  classical
  let v := copyModuleMap k r θ (pdCoordinateVector k r m a)
  let B := pdCoordinateBasis k r n
  have h (b) : B.repr v b = coordinateEntry k r θ a b := by
    change copyToCoordinate k r n v b = _
    unfold coordinateEntry coordinateChange
    simp only [LinearMap.comp_apply, coordinateToCopy_single, v]
  simpa only [h, B, pdCoordinateBasis_apply] using (B.sum_repr v).symm

private theorem coordinateOne_sum {m n : SimplexCategory} (θ : m ⟶ n)
    (a : pdCoordinates r m.len) :
    exteriorPower.map 1 (copyModuleMap k r θ) (pdCoordinateOne k r m a) =
      ∑ b, coordinateEntry k r θ a b • pdCoordinateOne k r n b := by
  unfold pdCoordinateOne
  rw [exteriorPower_map_one, coordinateVector_sum]
  simp only [map_sum, map_smul]

private theorem wedgeOne_sum {ι : Type*} {M : Type u} [Fintype ι] [AddCommGroup M] [Module k M]
    (j : ℕ) (c : ι → k) (v : ι → ⋀[k]^1 M) (w : ⋀[k]^j M) :
    DeRham.wedgeOne k M j (∑ i, c i • v i) w =
      ∑ i, c i • DeRham.wedgeOne k M j (v i) w := by
  apply Subtype.ext
  simp only [DeRham.wedgeOne_coe, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_mul, smul_mul_assoc]

/-- pd de Rham 微分は余面と余退化に自然。 -/
def pdDeRhamDifferential (j : ℕ) : pdRow p k r j ⟶ pdRow p k r (j+1) where
  app n := pdVerticalD p k r n j
  naturality m n θ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x w
    change pdTerm p k r m.len at x
    change ⋀[k]^j (CopyModule k r m) at w
    let mapForms (i : ℕ) := TensorProduct.map (pdTermMap p k r θ)
      (exteriorPower.map i (copyModuleMap k r θ))
    let dForms (a : SimplexCategory) := ∑ b : pdCoordinates r a.len, TensorProduct.map
      (pdPartial p k r a.len b)
      (DeRham.wedgeOne k (CopyModule k r a) j (pdCoordinateOne k r a b))
    change dForms n (mapForms j (x ⊗ₜ[k] w)) = mapForms (j+1) (dForms m (x ⊗ₜ[k] w))
    simp only [dForms, mapForms, TensorProduct.map_tmul, LinearMap.sum_apply, map_sum,
      pdPartial_chainRule, wedgeOne_map, coordinateOne_sum, TensorProduct.sum_tmul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [wedgeOne_sum, TensorProduct.tmul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact TensorProduct.smul_tmul _ _ _

open AlgebraicTopology
open scoped Simplicial

private abbrev pdRowComplex (j : ℕ) :=
  (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r j)

private theorem column_d_eq (n j : ℕ) :
    (pdDeRhamColumn p k r ⦋n⦌).d j (j+1) = pdVerticalD p k r ⦋n⦌ j := by
  dsimp only [pdDeRhamColumn, CochainComplex.of]
  exact CochainComplex.of_d _ _ j

set_option maxHeartbeats 1000000 in
-- 行と列の定義から隣接する微分の可換性を照合する。
/-- pd de Rham の余単体的な行と分冪微分の列をまとめた双複体。 -/
def pdDeRhamDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{u} k) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun ij => (pdRow p k r ij.2).obj ⦋ij.1⦌)
    (fun a b j => (pdRowComplex p k r j).d a b)
    (fun n i j => (pdDeRhamColumn p k r ⦋n⦌).d i j)
    (fun a b h j => (pdRowComplex p k r j).shape a b h)
    (fun n a b h => (pdDeRhamColumn p k r ⦋n⦌).shape a b h)
    (fun a b c j => (pdRowComplex p k r j).d_comp_d a b c)
    (fun n a b c => (pdDeRhamColumn p k r ⦋n⦌).d_comp_d a b c)
    (fun a b i j => by
      by_cases h : i+1 = j
      · subst j
        rw [column_d_eq, column_d_eq]
        exact (((alternatingCofaceMapComplex (ModuleCat.{u} k)).map
          (pdDeRhamDifferential p k r i)).comm a b).symm
      · rw [(pdDeRhamColumn p k r ⦋a⦌).shape i j h,
          (pdDeRhamColumn p k r ⦋b⦌).shape i j h]
        exact comp_zero.trans zero_comp.symm)

open SerrePositivity.HomologicalAlgebra

/-- pd de Rham 双複体の総複体。 -/
abbrev pdDeRhamTotal :=
  (pdDeRhamDoubleComplex p k r).total (ComplexShape.up ℕ)

/-- 総複体から第 0 行への射影。 -/
def pdDeRhamRowZeroProjection :
    pdDeRhamTotal p k r ⟶
      (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r 0) :=
  totalToRowZero (pdDeRhamDoubleComplex p k r)

/-- 総複体から第 0 列への射影。 -/
def pdDeRhamColumnZeroProjection :
    pdDeRhamTotal p k r ⟶ pdDeRhamColumn p k r ⦋0⦌ :=
  totalToColumnZero (pdDeRhamDoubleComplex p k r)

end SerrePositivity.BhattScholze.Prismatic
