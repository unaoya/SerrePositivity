module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization

/-!
概要：局所化の指定次数成分への写像は、和と合成を保つ。
方針：通常の局所化の写像へ戻し、分数を分子の写像で計算する。
規約：各分母の冪で許される分子の族を指定する。
使われ方：有限自由加群の成分射影と包含の分裂を Čech 複体へ移す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- 指定次数の局所化に誘導される写像は恒等写像を保つ。 -/
theorem projectiveGradedAwayMap_id (f : S) (V : ℕ → Submodule R M) :
    projectiveGradedAwayMap f V V LinearMap.id (fun _ _ h ↦ h) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change IsLocalizedModule.map (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) LinearMap.id z.val = z.val
  rw [IsLocalizedModule.map_id]
  rfl

/-- 指定次数の局所化に誘導される写像は和を保つ。 -/
theorem projectiveGradedAwayMap_add (f : S) (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (g h : M →ₗ[S] N) (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n)
    (hh : ∀ n, ∀ m ∈ V n, h m ∈ W n) :
    projectiveGradedAwayMap f V W (g + h)
        (fun n m hm ↦ (W n).add_mem (hg n m hm) (hh n m hm)) =
      projectiveGradedAwayMap f V W g hg + projectiveGradedAwayMap f V W h hh := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N) (g + h) z.val =
    IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N) g z.val +
    IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N) h z.val
  rw [map_add, LinearMap.add_apply]

/-- 指定次数の局所化に誘導される写像は合成を保つ。 -/
theorem projectiveGradedAwayMap_comp (f : S) (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (Z : ℕ → Submodule R P) (g : M →ₗ[S] N) (h : N →ₗ[S] P)
    (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n) (hh : ∀ n, ∀ m ∈ W n, h m ∈ Z n) :
    projectiveGradedAwayMap f V Z (h.comp g) (fun n m hm ↦ hh n _ (hg n m hm)) =
      (projectiveGradedAwayMap f W Z h hh).comp (projectiveGradedAwayMap f V W g hg) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) P) (h.comp g) z.val =
    IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) P) h
      (IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) N) g z.val)
  induction z.val using LocalizedModule.induction_on with
  | _ m s =>
    simp only [IsLocalizedModule.map_LocalizedModules, LinearMap.comp_apply]

/-- 単射な加群写像は、局所化の指定次数成分でも単射になる。 -/
theorem projectiveGradedAwayMap_injective (f : S) (V : ℕ → Submodule R M)
    (W : ℕ → Submodule R N) (g : M →ₗ[S] N)
    (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n) (hinj : Function.Injective g) :
    Function.Injective (projectiveGradedAwayMap f V W g hg) := by
  intro x y h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  exact IsLocalizedModule.map_injective (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) N) g hinj he

end SerrePositivity.AlgebraicGeometry
