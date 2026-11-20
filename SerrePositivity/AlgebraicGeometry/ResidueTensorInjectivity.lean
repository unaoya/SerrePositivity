module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
概要：KST §5、Stacks 05DH の特殊な局所化への準備となる剰余体による単射性の検出。
方針：剰余体上の基底の像の線形独立性を平坦性によって持ち上げる。
規約：加群の有限生成性は仮定しない。
使われ方：分裂表示を持つ代数の閉ファイバーによる単射性判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

omit [IsLocalRing R] in
/--
概要：二つの平坦加群の直積も平坦。
方針：テンソル積と有限直積の実同型で包含のテンソル化の単射性を成分へ分ける。
規約：KST §5、Stacks 05DH の準備、基礎環は任意の可換環。
使われ方：分裂部分加群の安定化による単射性判定。
-/
theorem flat_binaryProduct [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  apply Module.Flat.iff_lTensor_injectiveₛ.mpr
  intro P _ _ I
  let eI := TensorProduct.prodLeft R R M N I
  let eP := TensorProduct.prodLeft R R M N P
  let hM := I.subtype.lTensor M
  let hN := I.subtype.lTensor N
  have hsquare : eP.toLinearMap.comp (I.subtype.lTensor (M × N)) =
      (hM.prodMap hN).comp eI.toLinearMap := by
    ext m n <;> rfl
  intro x y hxy
  have h := congrArg eP hxy
  change (eP.toLinearMap.comp (I.subtype.lTensor (M × N))) x =
    (eP.toLinearMap.comp (I.subtype.lTensor (M × N))) y at h
  rw [hsquare] at h
  apply eI.injective
  apply Prod.ext
  · exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype
      Subtype.val_injective (congrArg Prod.fst h)
  · exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype
      Subtype.val_injective (congrArg Prod.snd h)

/--
概要：自由加群から平坦加群への写像は剰余体へのテンソル後の単射性から単射となる。
方針：基底の剰余体上の像の線形独立性を基礎環へ持ち上げる。
規約：KST §5、Stacks 05DH, Lemma 38.7.4 の準備、有限生成性は不要。
使われ方：分裂部分加群から平坦加群への単射性の検出。
-/
theorem injective_of_residueTensor_injective_of_free [Module.Free R M] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange (IsLocalRing.ResidueField R))) :
    Function.Injective f := by
  let k := IsLocalRing.ResidueField R
  let b := Module.Free.chooseBasis R M
  have hli : LinearIndependent k (fun i => (1 : k) ⊗ₜ[R] f (b i)) := by
    simpa only [Function.comp_def, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      one_smul] using (b.baseChange k).linearIndependent.map' (f.baseChange k)
        (LinearMap.ker_eq_bot.mpr hf)
  exact LinearMap.injective_of_linearIndependent b.span_eq
    (Module.IsLocalRing.linearIndependent_of_flat (f ∘ b) hli)

/--
概要：自由加群の実際の分裂部分加群から平坦加群への写像の単射性を剰余体で検出する。
方針：自由加群上の写像を像と分裂の補成分の直積へ安定化する。
規約：KST §5、Stacks 05DH, Lemma 38.7.4 の特殊形への準備、有限性は不要。
使われ方：分裂表示を持つ代数の特別な局所化への単射性。
-/
theorem injective_of_residueTensor_injective_of_retract
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Flat R N]
    (e : M →ₗ[R] F) (p : F →ₗ[R] M) (hpe : p.comp e = LinearMap.id)
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange (IsLocalRing.ResidueField R))) :
    Function.Injective f := by
  let k := IsLocalRing.ResidueField R
  let g : F →ₗ[R] N × F := (f.comp p).prod (LinearMap.id - e.comp p)
  let : Module.Flat R (N × F) := flat_binaryProduct
  have hfst : (LinearMap.fst R N F).comp g = f.comp p := rfl
  have hsnd : (LinearMap.snd R N F).comp g = LinearMap.id - e.comp p := rfl
  have hgk : Function.Injective (g.baseChange k) := by
    apply (injective_iff_map_eq_zero (g.baseChange k)).mpr
    intro z hz
    have hz1 := congrArg ((LinearMap.fst R N F).baseChange k) hz
    change (((LinearMap.fst R N F).baseChange k).comp (g.baseChange k)) z = 0 at hz1
    rw [← LinearMap.baseChange_comp, hfst, LinearMap.baseChange_comp] at hz1
    have hpz : p.baseChange k z = 0 :=
      hf (by simpa only [LinearMap.comp_apply, map_zero] using hz1)
    have hz2 := congrArg ((LinearMap.snd R N F).baseChange k) hz
    change (((LinearMap.snd R N F).baseChange k).comp (g.baseChange k)) z = 0 at hz2
    rw [← LinearMap.baseChange_comp, hsnd, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, LinearMap.baseChange_comp] at hz2
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hpz,
      map_zero, sub_zero] using hz2
  have hginj := injective_of_residueTensor_injective_of_free g hgk
  intro x y hxy
  have hpx : p (e x) = x := LinearMap.congr_fun hpe x
  have hpy : p (e y) = y := LinearMap.congr_fun hpe y
  have hge : g (e x) = g (e y) := by
    change (f (p (e x)), e x - e (p (e x))) = (f (p (e y)), e y - e (p (e y)))
    rw [hpx, hpy, hxy, sub_self, sub_self]
  simpa only [hpx, hpy] using congrArg p (hginj hge)

/--
概要：射影加群から平坦加群への写像の単射性は剰余体へのテンソル後に検出できる。
方針：射影加群の実際の自由加群への分裂を選び、分裂部分加群の場合を適用する。
規約：KST §5、Stacks 05DH, Lemma 38.7.4 の準備、射影加群の有限性は不要。
使われ方：幾何学的整な代数の特別な局所化での単射性。
-/
theorem injective_of_residueTensor_injective_of_projective
    [Module.Projective R M] [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange (IsLocalRing.ResidueField R))) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  exact injective_of_residueTensor_injective_of_retract e
    (Finsupp.linearCombination R id) he f hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
