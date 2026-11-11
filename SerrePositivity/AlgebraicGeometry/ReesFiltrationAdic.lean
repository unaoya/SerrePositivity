module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationExact

/-!
概要：I 進 Rees 加群の全射と、写像の核から得るフィルトレーションを扱う。
方針：イデアルの冪の作用と線形写像の像を交換し、核との交叉に安定性を適用する。
規約：核のフィルトレーションは、元のフィルトレーションとの交叉で定める。
使われ方：形式関数の長完全列に使う Rees 加群の短完全列。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (I : Ideal R)

/-- 線形写像が I 進フィルトレーションから誘導する Rees 加群の写像。 -/
def reesAdicMap (f : M →ₗ[R] N) :
    (I.stableFiltration (⊤ : Submodule R M)).submodule →ₗ[reesAlgebra I]
      (I.stableFiltration (⊤ : Submodule R N)).submodule :=
  reesFiltrationMap (I.stableFiltration ⊤) (I.stableFiltration ⊤) f
    (fun n m hm ↦ Submodule.smul_top_le_comap_smul_top (I ^ n) f hm)

/-- 全射な加群写像は、I 進 Rees 加群にも全射を与える。 -/
theorem reesAdicMap_surjective (f : M →ₗ[R] N) (hs : Function.Surjective f) :
    Function.Surjective (reesAdicMap I f) := by
  apply reesFiltrationMap_surjective
  intro n y hy
  have hmap : (I ^ n • (⊤ : Submodule R M)).map f = I ^ n • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hs]
  have hym : y ∈ (I ^ n • (⊤ : Submodule R M)).map f := hmap.symm ▸ hy
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hym
  exact ⟨⟨x, hx⟩, hxy⟩

variable {I} (F : I.Filtration M)

/-- 元のフィルトレーションと写像の核との交叉。 -/
def reesKernelFiltration (f : M →ₗ[R] N) : I.Filtration M :=
  F ⊓ I.trivialFiltration (LinearMap.ker f)

/-- 核との交叉から、元の Rees 加群への包含。 -/
def reesKernelInclusion (f : M →ₗ[R] N) :
    (reesKernelFiltration F f).submodule →ₗ[reesAlgebra I] F.submodule :=
  reesFiltrationMap (reesKernelFiltration F f) F LinearMap.id (fun _ _ h ↦ h.1)

/-- 核との交叉から得る Rees 加群の包含は単射。 -/
theorem reesKernelInclusion_injective (f : M →ₗ[R] N) :
    Function.Injective (reesKernelInclusion F f) :=
  reesFiltrationMap_injective (reesKernelFiltration F f) F LinearMap.id
    (fun _ _ h ↦ h.1) Function.injective_id

/-- 核との交叉は、Rees 加群の写像の核を各次数で実現する。 -/
theorem reesKernelInclusion_exact (G : I.Filtration N) (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) :
    Function.Exact (reesKernelInclusion F f) (reesFiltrationMap F G f hf) := by
  apply reesFiltrationMap_exact (reesKernelFiltration F f) F G LinearMap.id f
    (fun _ _ h ↦ h.1) hf
  intro n y hy
  constructor
  · intro hz
    exact ⟨⟨y, ⟨hy, hz⟩⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property.2

/-- Noether 環上の有限加群では、安定なフィルトレーションと核との交叉も安定。 -/
theorem reesKernelFiltration_stable [IsNoetherianRing R] [Module.Finite R M]
    (f : M →ₗ[R] N) (hF : F.Stable) : (reesKernelFiltration F f).Stable :=
  hF.inter_right (I.trivialFiltration (LinearMap.ker f))

/-- 核との交叉の Rees 加群は、安定な場合に有限生成。 -/
theorem reesKernelModule_finite [IsNoetherianRing R] [Module.Finite R M]
    (f : M →ₗ[R] N) (hF : F.Stable) :
    Module.Finite (reesAlgebra I) (reesKernelFiltration F f).submodule :=
  reesFiltration_finite _ (reesKernelFiltration_stable F f hF)

end SerrePositivity.AlgebraicGeometry
