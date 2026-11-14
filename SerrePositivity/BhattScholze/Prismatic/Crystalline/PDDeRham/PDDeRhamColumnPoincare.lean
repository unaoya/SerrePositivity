module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDColumnCoordinateEvaluation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCollapse
public import SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDColumnContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCollapse
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
public import Mathlib.Algebra.Homology.QuasiIso
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex

/-!
# 全差座標の評価の基底上の表示

## 概要
第 0 頂点への余単体評価を、分冪単項式と一次形式の座標基底で計算する。

## 方針
分冪単項式の指数が正の因子と、差座標の一次形式を零にする。

## 規約
多項式の第 0 頂点座標はそのまま。

## 使われ方
一座標ごとの分冪 Poincaré 収縮と、列の余単体評価の照合。
-/

public noncomputable section

open CategoryTheory DividedPowerAlgebra SerrePositivity.DeRham
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ) (n : SimplexCategory)

local notation "θ" => SimplexCategory.const n n 0

private theorem const_diffMap : diffMap k r θ = 0 := by
  apply (Finsupp.basisSingleOne (R := k)).ext
  rintro ⟨j, i⟩
  change diffMap k r θ (vertexDiff k r n j i.succ) = 0
  rw [diffMap_vertex]
  simp

private theorem const_pdRawMap_left :
    (pdRawMap k r θ).comp Algebra.TensorProduct.includeLeft = Algebra.TensorProduct.includeLeft := by
  rw [pdRawMap_left]
  apply MvPolynomial.algHom_ext
  intro j
  rw [MvPolynomial.aeval_X]
  simp [copy, baseVar, vertexDiff]

private theorem map_zero_freeDPMonomial (m : (Fin r × Fin n.len) →₀ ℕ) :
    DividedPowerAlgebra.map k (0 : Diff k r n →ₗ[k] Diff k r n)
      (freeDPMonomial _ k m) = if m = 0 then 1 else 0 := by
  classical
  unfold freeDPMonomial Finsupp.prod
  split_ifs with h
  · subst m
    simp
  · rw [map_prod]
    obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty (by
      intro hh
      exact h (Finsupp.support_eq_empty.mp hh))
    apply Finset.prod_eq_zero ha
    rw [DividedPowerAlgebra.map_apply_dp, LinearMap.zero_apply]
    exact dp_null_of_ne_zero (Finsupp.mem_support_iff.mp ha)

/-- 頂点を潰す写像は、分冪の指数が全零の基底成分だけを残す。 -/
private theorem pdRawMap_const_basis (m : (Fin r →₀ ℕ) × ((Fin r × Fin n.len) →₀ ℕ)) :
    pdRawMap k r θ (pdRawBasis k r n.len m) = if m.2 = 0 then pdRawBasis k r n.len m else 0 := by
  rw [pdRawBasis, Module.Basis.tensorProduct_apply', freeDPBasis_apply, MvPolynomial.coe_basisMonomials]
  let f := MvPolynomial.monomial m.1 (1 : k)
  let g := freeDPMonomial (Fin r × Fin n.len) k m.2
  change pdRawMap k r θ (f ⊗ₜ[k] g) = if m.2 = 0 then f ⊗ₜ[k] g else 0
  have h := DFunLike.congr_fun (const_pdRawMap_left k r n) f
  have h' := DFunLike.congr_fun (pdRawMap_right k r θ) g
  simp only [AlgHom.comp_apply] at h h'
  rw [const_diffMap, map_zero_freeDPMonomial] at h'
  have ht (x : MvPolynomial (Fin r) k) (y : DividedPowerAlgebra k (Diff k r n)) :
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) x : pdRaw k r n.len) *
        Algebra.TensorProduct.includeRight y = x ⊗ₜ[k] y := by
    change (x ⊗ₜ[k] 1) * (1 ⊗ₜ[k] y) = _
    simp
  rw [← ht, map_mul, h, h']
  split_ifs with he
  · have hg : g = 1 := by simp [g, he, freeDPMonomial, Finsupp.prod]
    rw [hg, ht]
  · rw [map_zero, mul_zero]

/-- 頂点を潰す写像は、第 0 頂点の一次座標を保つ。 -/
private theorem copyModuleMap_const_base (t : Fin r) :
    copyModuleMap k r θ (pdCoordinateBasis k r n (.inl t)) =
      pdCoordinateBasis k r n (.inl t) := by
  simp only [pdCoordinateBasis_apply]
  change copyModuleMap k r θ (Finsupp.single (t, 0) 1) = Finsupp.single (t, 0) 1
  rw [copyModuleMap_single, SimplexCategory.const_apply]

/-- 頂点を潰す写像は、差座標の一次形式を零に送る。 -/
private theorem copyModuleMap_const_diff (s : Fin r × Fin n.len) :
    copyModuleMap k r θ (pdCoordinateBasis k r n (.inr s)) = 0 := by
  rw [pdCoordinateBasis_apply]
  change copyModuleMap k r θ
    (Finsupp.single (s.1, s.2.succ) 1 - Finsupp.single (s.1, 0) 1) = 0
  rw [map_sub, copyModuleMap_single, copyModuleMap_single,
    SimplexCategory.const_apply, SimplexCategory.const_apply, sub_self]

private theorem pdRawConstantTerm_basis (s : Fin r × Fin n.len)
    (m : (Fin r →₀ ℕ) × ((Fin r × Fin n.len) →₀ ℕ)) :
    pdRawConstantTerm k r n.len s (pdRawBasis k r n.len m) =
      if m.2 s = 0 then pdRawBasis k r n.len m else 0 := by
  unfold pdRawConstantTerm pdRawBasis
  rw [Module.Basis.tensorProduct_apply', TensorProduct.map_tmul, LinearMap.id_apply,
    freeDPBasis_apply, freeDPConstantTerm_monomial]
  split_ifs <;> simp

private abbrev DS := Fin r × Fin n.len

private def allCoefficientsEval (L : List (DS r n)) : pdRaw k r n.len →ₗ[k] pdRaw k r n.len :=
  L.foldr (fun s f => (pdRawConstantTerm k r n.len s).comp f) LinearMap.id

private theorem allCoefficientsEval_basis (L : List (DS r n))
    (m : (Fin r →₀ ℕ) × ((DS r n) →₀ ℕ)) :
    allCoefficientsEval k r n L (pdRawBasis k r n.len m) =
      if ∀ s ∈ L, m.2 s = 0 then pdRawBasis k r n.len m else 0 := by
  classical
  induction L with
  | nil => simp [allCoefficientsEval]
  | cons s L ih =>
    change pdRawConstantTerm k r n.len s (allCoefficientsEval k r n L (pdRawBasis k r n.len m)) = _
    rw [ih]
    by_cases h : ∀ a ∈ L, m.2 a = 0
    · rw [ite_eq_left h, pdRawConstantTerm_basis]
      by_cases hs : m.2 s = 0
      · have he : ∀ a ∈ s :: L, m.2 a = 0 := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hs
          · exact h a ha
        rw [ite_eq_left hs, ite_eq_left he]
      · rw [ite_eq_right hs, ite_eq_right (fun e => hs (e s List.mem_cons_self))]
    · rw [ite_eq_right h, map_zero, ite_eq_right (fun e => h (fun a ha => e a (List.mem_cons_of_mem _ ha)))]

private theorem allCoefficientsEval_const (L : List (DS r n)) (h : ∀ s, s ∈ L) :
    allCoefficientsEval k r n L = (pdRawMap k r θ).toLinearMap := by
  apply (pdRawBasis k r n.len).ext
  intro m
  rw [allCoefficientsEval_basis, AlgHom.toLinearMap_apply, pdRawMap_const_basis]
  have he : (∀ s ∈ L, m.2 s = 0) ↔ m.2 = 0 := by
    constructor
    · intro h'
      ext s
      exact h' s (h s)
    · intro h' s _
      exact DFunLike.congr_fun h' s
  by_cases hz : m.2 = 0
  · rw [ite_eq_left (he.mpr hz), ite_eq_left hz]
  · rw [ite_eq_right (fun e => hz (he.mp e)), ite_eq_right hz]

private def copyEval (s : DS r n) : CopyModule k r n →ₗ[k] CopyModule k r n :=
  exteriorCoordinateProjection ((pdCoordinateBasis k r n).coord (.inr s))
    (pdCoordinateBasis k r n (.inr s))

private theorem copyEval_basis (s : DS r n) (a : pdCoordinates r n.len) :
    copyEval k r n s (pdCoordinateBasis k r n a) =
      if a = .inr s then 0 else pdCoordinateBasis k r n a := by
  classical
  unfold copyEval exteriorCoordinateProjection
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst a
    simp
  · simp

private def allCopyEval (L : List (DS r n)) : CopyModule k r n →ₗ[k] CopyModule k r n :=
  L.foldr (fun s f => (copyEval k r n s).comp f) LinearMap.id

private theorem allCopyEval_basis_base (L : List (DS r n)) (t : Fin r) :
    allCopyEval k r n L (pdCoordinateBasis k r n (.inl t)) = pdCoordinateBasis k r n (.inl t) := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    change copyEval k r n s (allCopyEval k r n L (pdCoordinateBasis k r n (.inl t))) = _
    rw [ih, copyEval_basis]
    simp

private theorem allCopyEval_basis_diff (L : List (DS r n)) (t : DS r n) :
    allCopyEval k r n L (pdCoordinateBasis k r n (.inr t)) =
      if t ∈ L then 0 else pdCoordinateBasis k r n (.inr t) := by
  classical
  induction L with
  | nil => simp [allCopyEval]
  | cons s L ih =>
    change copyEval k r n s (allCopyEval k r n L (pdCoordinateBasis k r n (.inr t))) = _
    rw [ih]
    by_cases h : t ∈ L
    · simp [h]
    · simp [h, copyEval_basis]

private theorem allCopyEval_const (L : List (DS r n)) (h : ∀ s, s ∈ L) :
    allCopyEval k r n L = copyModuleMap k r θ := by
  apply (pdCoordinateBasis k r n).ext
  rintro (t | s)
  · rw [allCopyEval_basis_base, copyModuleMap_const_base]
  · rw [allCopyEval_basis_diff, copyModuleMap_const_diff, ite_eq_left (h s)]

variable (p : ℕ) (hp : (p : k) = 0)
local notation "K" => pdRawDeRhamColumn p k r hp n

private def allCoordinateEval (L : List (DS r n)) : K ⟶ K :=
  L.foldr (fun s f => f ≫ pdRawCoordinateEvaluation p k r hp n s) (𝟙 K)

private theorem coordinateEval_f (s : DS r n) (j : ℕ) :
    (pdRawCoordinateEvaluation p k r hp n s).f j =
      ModuleCat.ofHom (TensorProduct.map (pdRawConstantTerm k r n.len s)
        (exteriorPower.map j (copyEval k r n s))) := by
  cases j with
  | zero =>
    rw [pdRawCoordinateEvaluation_zero, copyEval, exteriorPower_map_coordinateProjection_zero]
  | succ j => exact pdRawCoordinateEvaluation_succ p k r hp n s j

private theorem allCoordinateEval_f (L : List (DS r n)) (j : ℕ) :
    (allCoordinateEval k r n p hp L).f j =
      ModuleCat.ofHom (TensorProduct.map (allCoefficientsEval k r n L)
        (exteriorPower.map j (allCopyEval k r n L))) := by
  induction L with
  | nil =>
    simp [allCoordinateEval, allCoefficientsEval, allCopyEval, TensorProduct.map_id]
    rfl
  | cons s L ih =>
    change (allCoordinateEval k r n p hp L ≫ pdRawCoordinateEvaluation p k r hp n s).f j = _
    rw [HomologicalComplex.comp_f, ih, coordinateEval_f]
    apply ModuleCat.hom_ext
    change (TensorProduct.map (pdRawConstantTerm k r n.len s) (exteriorPower.map j (copyEval k r n s))).comp
      (TensorProduct.map (allCoefficientsEval k r n L) (exteriorPower.map j (allCopyEval k r n L))) = _
    rw [← TensorProduct.map_comp, ← exteriorPower.map_comp]
    rfl

private def allCoordinateEvalHomotopy (L : List (DS r n)) :
    Homotopy (allCoordinateEval k r n p hp L) (𝟙 K) :=
  match L with
  | [] => Homotopy.refl _
  | s :: L => ((allCoordinateEvalHomotopy L).comp
      (pdRawCoordinateEvaluationHomotopy p k r hp n s)).trans
        (Homotopy.ofEq (Category.id_comp _))

private theorem allCoordinateEval_iso (L : List (DS r n)) (hL : ∀ s, s ∈ L) :
    allCoordinateEval k r n p hp L ≫ (pdRawDeRhamColumnIso p k r hp n).hom =
      (pdRawDeRhamColumnIso p k r hp n).hom ≫ pdDeRhamColumnMap p k r θ := by
  ext j : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, allCoordinateEval_f,
    allCoefficientsEval_const k r n L hL, allCopyEval_const k r n L hL]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  let E := pdRawFormsEquiv p k r hp n j
  change E (TensorProduct.map (pdRawMap k r θ).toLinearMap
      (exteriorPower.map j (copyModuleMap k r θ)) (f ⊗ₜ[k] w)) =
    TensorProduct.map (pdTermMap p k r θ) (exteriorPower.map j (copyModuleMap k r θ))
      (E (f ⊗ₜ[k] w))
  simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, E, pdRawFormsEquiv_tmul,
    pdRawToTerm_eq_unit]
  exact congrArg (fun z : pdTerm p k r n.len => z ⊗ₜ[k] exteriorPower.map j (copyModuleMap k r θ) w)
    (pdTermMap_unit p k r θ f).symm

private theorem pdDeRhamColumnMap_comp {m n l : SimplexCategory} (f : m ⟶ n) (g : n ⟶ l) :
    pdDeRhamColumnMap p k r f ≫ pdDeRhamColumnMap p k r g =
      pdDeRhamColumnMap p k r (f ≫ g) := by
  ext j : 1
  exact ((pdRow p k r j).map_comp f g).symm

/-- 標数 p では、各列から差座標を消す写像はホモトピー同値。 -/
def pdDeRhamColumnCollapseHomotopyEquiv :
    HomotopyEquiv (pdDeRhamColumn p k r n) (pdDeRhamColumn p k r ⦋0⦌) where
  hom := pdDeRhamColumnCollapse p k r n
  inv := pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ n 0)
  homotopyInvHomId := Homotopy.ofEq (pdDeRhamColumnCollapse_split p k r n)
  homotopyHomInvId := by
    classical
    let L := (Finset.univ : Finset (DS r n)).toList
    let E := pdRawDeRhamColumnIso p k r hp n
    have hL (s) : s ∈ L := by simp [L]
    have h := (allCoordinateEvalHomotopy k r n p hp L).compRightId E.hom
    have h' : Homotopy (E.hom ≫ pdDeRhamColumnMap p k r θ) E.hom := by
      exact (Homotopy.ofEq (allCoordinateEval_iso k r n p hp L hL).symm).trans h
    have h'' := h'.compLeft E.inv
    have hθ : pdDeRhamColumnCollapse p k r n ≫
        pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ n 0) =
          pdDeRhamColumnMap p k r θ := by
      rw [pdDeRhamColumnCollapse, pdDeRhamColumnMap_comp, collapseSimplex,
        ← SimplexCategory.const_fac_thru_zero]
    rw [hθ]
    simpa only [← Category.assoc, E.inv_hom_id, Category.id_comp] using h''

include hp in
/-- 標数 p では、各列から第 0 列への座標評価が擬同型を誘導する。 -/
theorem pdDeRhamColumnCollapse_quasiIso : QuasiIso (pdDeRhamColumnCollapse p k r n) := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (pdDeRhamColumnCollapseHomotopyEquiv k r n p hp).toHomologyIso i |>.isIso_hom

include hp in
/-- 標数 p では、差座標を消す双複体の写像は総複体上で擬同型。 -/
theorem pdDeRhamCollapse_total_quasiIso :
    QuasiIso (HomologicalComplex₂.total.map (pdDeRhamCollapse p k r) (ComplexShape.up ℕ)) := by
  apply SerrePositivity.HomologicalAlgebra.bicomplexTotal_quasiIso_of_columns
  · intro a
    exact pdDeRhamColumnCollapse_quasiIso k r ⦋a⦌ p hp
  · intro a b x
    let f := pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ ⦋a⦌ 0)
    refine ⟨f.f b x, ?_⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun g => g.f b) (pdDeRhamColumnCollapse_split p k r ⦋a⦌)) x

end SerrePositivity.BhattScholze.Prismatic
