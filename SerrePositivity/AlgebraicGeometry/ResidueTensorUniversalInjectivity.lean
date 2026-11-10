module

public import SerrePositivity.AlgebraicGeometry.ResidueTensorInjectivity
import Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
概要：局所環上で剰余体に移すと単射になる、射影加群から平坦加群への写像は普遍単射。
方針：テンソル関係の有限個の係数を、剰余体で単射な有限自由加群間の写像へ移す。
規約：普遍単射性は任意の加群とのテンソル積について述べる。
使われ方：幾何学的整なファイバーの生成点で選んだ基底を平坦化の帰納に使う。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct BigOperators

variable {R N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N]

omit [IsLocalRing R] in
private theorem lTensor_injective_of_split
    {S T Q : Type*} [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
    [AddCommGroup Q] [Module R Q] (a : S →ₗ[R] T) (b : T →ₗ[R] S)
    (h : b.comp a = LinearMap.id) : Function.Injective (a.lTensor Q) := by
  have hQ : (b.lTensor Q).comp (a.lTensor Q) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, h, LinearMap.lTensor_id]
  exact (show Function.LeftInverse (b.lTensor Q) (a.lTensor Q) from
    fun x => LinearMap.congr_fun hQ x).injective

private theorem lTensor_injective_of_residue_finsupp {ι : Type*} [Module.Flat R N]
    (f : (ι →₀ R) →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)))
    (Q : Type*) [AddCommGroup Q] [Module R Q] : Function.Injective (f.lTensor Q) := by
  classical
  let k := IsLocalRing.ResidueField R
  apply (injective_iff_map_eq_zero (f.lTensor Q)).mpr
  intro x hx
  let e := TensorProduct.finsuppScalarRight R R Q ι
  let c := e x
  let s := c.support
  let i : (s →₀ R) →ₗ[R] ι →₀ R := Finsupp.lmapDomain R R Subtype.val
  let j : (ι →₀ R) →ₗ[R] s →₀ R := Finsupp.lcomapDomain Subtype.val Subtype.val_injective
  have hji : j.comp i = LinearMap.id :=
    LinearMap.ext (Finsupp.leftInverse_lcomapDomain_mapDomain
      (R := R) (M := R) Subtype.val Subtype.val_injective)
  let y : Q ⊗[R] (s →₀ R) := ∑ v : s, c v ⊗ₜ[R] Finsupp.single v 1
  have hiy : i.lTensor Q y = x := by
    apply e.injective
    ext v
    change e (i.lTensor Q y) v = c v
    simp only [y, map_sum, LinearMap.lTensor_tmul, i, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, Finsupp.finsetSum_apply, e,
      TensorProduct.finsuppScalarRight_apply_tmul_apply]
    rw [Finset.sum_coe_sort s (fun w => (Finsupp.single w (1 : R)) v • c w)]
    by_cases hv : v ∈ s
    · rw [Finset.sum_eq_single v]
      · simp
      · intro w _ h
        simp [Finsupp.single_eq_of_ne (Ne.symm h)]
      · exact fun h => (h hv).elim
    · rw [Finsupp.notMem_support_iff.mp hv]
      exact Finset.sum_eq_zero fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp [Finsupp.single_eq_of_ne (Ne.symm hne)]
  let g := f.comp i
  have hy : g.lTensor Q y = 0 := by rw [LinearMap.lTensor_comp_apply, hiy, hx]
  let v (a : s) := g (Finsupp.single a 1)
  have hsum : ∑ a : s, c a ⊗ₜ[R] v a = 0 := by
    simpa only [y, map_sum, LinearMap.lTensor_tmul, v] using hy
  obtain ⟨n, a, w, hav, hzero⟩ :=
    TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) hsum
  let α : (s →₀ R) →ₗ[R] (Fin n →₀ R) :=
    Finsupp.linearCombination R (fun v => Finsupp.equivFunOnFinite.symm (a v))
  let β : (Fin n →₀ R) →ₗ[R] N := Finsupp.linearCombination R w
  have hαone (u : s) : α (Finsupp.single u 1) = Finsupp.equivFunOnFinite.symm (a u) := by
    change Finsupp.linearCombination R _ (Finsupp.single u 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  have hcomp : β.comp α = g := by
    apply Finsupp.lhom_ext
    intro u t
    have hunit : (β.comp α) (Finsupp.single u 1) = g (Finsupp.single u 1) := by
      rw [LinearMap.comp_apply, hαone]
      change (Finsupp.equivFunOnFinite.symm (a u)).sum (fun i r => r • w i) = _
      rw [Finsupp.sum_fintype (Finsupp.equivFunOnFinite.symm (a u))
        (fun i r => r • w i) (fun i => zero_smul R (w i))]
      exact (hav u).symm
    rw [← Finsupp.smul_single_one u t, map_smul, map_smul, hunit]
  have hα : Function.Injective (α.lTensor k) := by
    intro u v h
    apply (hf.comp (lTensor_injective_of_split (Q := k) i j hji))
    change (f.lTensor k) (i.lTensor k u) = (f.lTensor k) (i.lTensor k v)
    rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    change g.lTensor k u = g.lTensor k v
    rw [← hcomp, LinearMap.lTensor_comp_apply, LinearMap.lTensor_comp_apply, h]
  obtain ⟨ρ, hρ⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective α).mpr hα
  have hαy : α.lTensor Q y = 0 := by
    apply (TensorProduct.finsuppScalarRight R R Q (Fin n)).injective
    ext j'
    simp only [y, map_sum, LinearMap.lTensor_tmul, Finsupp.finsetSum_apply,
      TensorProduct.finsuppScalarRight_apply_tmul_apply, hαone,
      Finsupp.equivFunOnFinite_symm_apply_apply, map_zero, Finsupp.zero_apply]
    exact hzero j'
  have hy₀ : y = 0 := (lTensor_injective_of_split (Q := Q) α ρ hρ)
    (hαy.trans (map_zero _).symm)
  rw [← hiy, hy₀, map_zero]

/--
概要：局所環上の射影加群から平坦加群への写像が剰余体への基底変更で単射なら、
任意の加群とテンソルしても単射。
方針：自由加群への分裂の補成分を付け加え、有限個のテンソル係数の関係を調べる。
規約：加群の有限生成性は仮定しない。
使われ方：生成点で選んだ基底による写像の普遍単射性。
-/
theorem lTensor_injective_of_residueTensor_injective_of_projective
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)))
    (Q : Type*) [AddCommGroup Q] [Module R Q] : Function.Injective (f.lTensor Q) := by
  let k := IsLocalRing.ResidueField R
  obtain ⟨i, hi⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  let F := M →₀ R
  let p : F →ₗ[R] M := Finsupp.linearCombination R id
  let g : F →ₗ[R] N × F := (f.comp p).prod (LinearMap.id - i.comp p)
  let : Module.Flat R (N × F) := flat_binaryProduct
  have hgk : Function.Injective (g.lTensor k) := by
    apply (injective_iff_map_eq_zero (g.lTensor k)).mpr
    intro z hz
    have hz1 := congrArg ((LinearMap.fst R N F).lTensor k) hz
    change (((LinearMap.fst R N F).lTensor k).comp (g.lTensor k)) z = _ at hz1
    rw [← LinearMap.lTensor_comp, show (LinearMap.fst R N F).comp g = f.comp p from rfl,
      LinearMap.lTensor_comp_apply, map_zero] at hz1
    have hpz : p.lTensor k z = 0 := hf (hz1.trans (map_zero _).symm)
    have hz2 := congrArg ((LinearMap.snd R N F).lTensor k) hz
    change (((LinearMap.snd R N F).lTensor k).comp (g.lTensor k)) z = _ at hz2
    rw [← LinearMap.lTensor_comp, show (LinearMap.snd R N F).comp g =
      LinearMap.id - i.comp p from rfl, LinearMap.lTensor_sub, LinearMap.lTensor_id,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.lTensor_comp_apply, hpz,
      map_zero, sub_zero, map_zero] at hz2
    exact hz2
  have hgQ := lTensor_injective_of_residue_finsupp g hgk Q
  have hgi : g.comp i = (LinearMap.inl R N F).comp f := by
    apply LinearMap.ext
    intro m
    apply Prod.ext
    · change f (p (i m)) = f m
      rw [show p (i m) = m from LinearMap.congr_fun hi m]
    · change i m - i (p (i m)) = 0
      rw [show p (i m) = m from LinearMap.congr_fun hi m, sub_self]
  intro x y hxy
  apply lTensor_injective_of_split (Q := Q) i p hi
  apply hgQ
  rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hgi,
    LinearMap.lTensor_comp_apply, LinearMap.lTensor_comp_apply, hxy]

/--
概要：局所環上の射影加群から平坦加群への写像が剰余体への基底変更で単射なら、
その余核は平坦。
方針：任意のテンソルでの単射性と、二つの右完全列の比較を使う。
規約：余核は値域による商加群。
使われ方：平坦化の帰納で生成点で選んだ基底を取り除く。
-/
theorem flat_cokernel_of_residueTensor_injective_of_projective
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  apply Module.Flat.iff_lTensor_injectiveₛ.mpr
  intro Q _ _ I
  let : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := f) (f₂ := (LinearMap.range f).mkQ) (g₁ := I.subtype) (g₂ := I.mkQ)
    f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp
      (lTensor_injective_of_residueTensor_injective_of_projective f hf (Q ⧸ I)))
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

end SerrePositivity.AlgebraicGeometry
