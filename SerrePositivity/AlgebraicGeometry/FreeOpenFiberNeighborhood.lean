module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：整な指定ファイバーに交わる自由化主開を、基底の近傍の全ファイバーに交わらせる。
方針：開写像による主開の像の中に、指定点を含む基底の主開を取る。
規約：自由化元がファイバー環で非零であることを主開との交わりに対応させる。
使われ方：Stacks 0815 で、一つの自由化写像の余核の台の次元を近傍全体で下げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：開なスペクトル写像で、元が整な指定ファイバーで非零なら、基底の主近傍の全ファイバーで非零。
方針：整なファイバーの生成点を使って、指定点が自由化主開の像に属することを示す。
規約：整域性は指定ファイバーだけに仮定する。
使われ方：Stacks 0815 の自由化主開が基底に全射になるよう縮める段階。
-/
theorem exists_base_basicOpen_of_nonzero_in_fiber
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R B))) (p : PrimeSpectrum R)
    [IsDomain (p.asIdeal.Fiber B)] (b : B)
    (hb : ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] b) ≠ 0) :
    ∃ a : R, a ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum R, a ∉ q.asIdeal →
      ((1 : q.asIdeal.ResidueField) ⊗ₜ[R] b) ≠ 0 := by
  let f := PrimeSpectrum.comap (algebraMap R B)
  let D : Set (PrimeSpectrum B) := PrimeSpectrum.basicOpen b
  let e := PrimeSpectrum.preimageHomeomorphFiber R B p
  let x := e.symm (⊥ : PrimeSpectrum (p.asIdeal.Fiber B))
  have hx : x.1 ∈ D := by
    change ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] b) ∉ (⊥ : Ideal (p.asIdeal.Fiber B))
    exact fun hz => hb (Ideal.mem_bot.mp hz)
  have hp : p ∈ f '' D := ⟨x.1, hx, x.2⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, hEq⟩, ha, hD⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp
      (hopen D (PrimeSpectrum.basicOpen b).isOpen)
  rw [← hEq] at ha hD
  refine ⟨a, ha, fun q hq hz => ?_⟩
  obtain ⟨z, hzD, hzq⟩ := hD hq
  let e' := PrimeSpectrum.preimageHomeomorphFiber R B q
  let w := e' ⟨z, hzq⟩
  have hw : w.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[R] q.asIdeal.Fiber B).toRingHom = z :=
    congrArg Subtype.val (e'.symm_apply_apply ⟨z, hzq⟩)
  apply hzD
  rw [← hw]
  change ((1 : q.asIdeal.ResidueField) ⊗ₜ[R] b) ∈ w.asIdeal
  rw [hz]
  exact Ideal.zero_mem _


/--
概要：平坦代数で拡大素イデアルに属さない元は、剰余体ファイバーでも非零。
方針：基底の素イデアルによる商から剰余体への単射を、平坦なテンソル積で保つ。
規約：基底は局所環に限定しない。
使われ方：ブローアップの標準チャート上で自由化元が指定ファイバーと交わることを確かめる。
-/
theorem fiber_tmul_ne_zero_of_not_mem_map
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    (p : Ideal R) [p.IsPrime] (b : B) (hb : b ∉ p.map (algebraMap R B)) :
    ((1 : p.ResidueField) ⊗ₜ[R] b) ≠ 0 := by
  intro hz
  let i := (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap
  have hi : Function.Injective i := IsFractionRing.injective (R ⧸ p) p.ResidueField
  have hzero : ((1 : R ⧸ p) ⊗ₜ[R] b) = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := B) i hi
    simpa [i] using hz
  have hmem : b ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ p) B 1) := hzero
  rw [LinearMap.ker_tensorProductMk, Ideal.smul_top_eq_map] at hmem
  exact hb hmem

end SerrePositivity.AlgebraicGeometry
