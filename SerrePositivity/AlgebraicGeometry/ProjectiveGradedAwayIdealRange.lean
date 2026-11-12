module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayIdeal

/-!
概要：各分子の像がイデアル倍なら、斉次局所化の写像の像もイデアル倍になる。
方針：イデアル倍の分子族への全射を作り、元の成分へ入れ直す。
規約：flat を仮定せず、像の等式を入力の分子族から導く。
使われ方：Rees の閉厚化の標準開の核の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R S N M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (I : Ideal R) (f : S) (V : ℕ → Submodule R N) (W : ℕ → Submodule R M)
variable (g : N →ₗ[S] M) (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n)
variable (himages : ∀ n, (V n).map (g.restrictScalars R) = I • W n)
variable (hstep : ∀ n (m : W n), f • m.val ∈ W (n + 1))

include himages hstep in
/-- 分子ごとの像の等式は、斉次局所化の像を元の指定成分のイデアル倍にする。 -/
theorem projectiveGradedAwayMap_range_ideal :
    LinearMap.range (projectiveGradedAwayMap f V W g hg) =
      I • (⊤ : Submodule R (projectiveGradedAway f W)) := by
  have hI : ∀ n, ∀ m ∈ V n, g m ∈ I • W n := by
    intro n m hm
    rw [← himages n]
    exact ⟨m, hm, rfl⟩
  let F := projectiveGradedAwayMap f V (fun n ↦ I • W n) g hI
  have hstepI : ∀ n (m : ↥(I • W n)), f • m.val ∈ I • W (n + 1) := by
    intro n m
    refine Submodule.smul_induction_on m.property ?_ ?_
    · intro r hr x hx
      rw [smul_comm f r]
      exact Submodule.smul_mem_smul hr (hstep n ⟨x, hx⟩)
    · intro x y hx hy
      rw [smul_add]
      exact (I • W (n + 1)).add_mem hx hy
  have hF : Function.Surjective F := by
    apply projectiveGradedAwayMap_surjective f V (fun n ↦ I • W n) g hI hstepI
    intro n w
    have hw : w.val ∈ (V n).map (g.restrictScalars R) := by
      rw [himages n]
      exact w.property
    obtain ⟨x, hx, he⟩ := hw
    exact ⟨⟨x, hx⟩, he⟩
  have htop : (I • (⊤ : Submodule R (projectiveGradedAway f W))).map
      (projectiveGradedAway f W).subtype = projectiveGradedAway f (fun n ↦ I • W n) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      projectiveGradedAway_ideal_smul]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (projectiveGradedAwayMap f V W g hg x).val ∈
        projectiveGradedAway f (fun n ↦ I • W n) := (F x).property
    rw [← htop] at hx
    obtain ⟨z, hz, he⟩ := hx
    exact (show z = projectiveGradedAwayMap f V W g hg x from Subtype.ext he) ▸ hz
  · intro hy
    have hy' : y.val ∈ projectiveGradedAway f (fun n ↦ I • W n) := by
      rw [← htop]
      exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := hF ⟨y.val, hy'⟩
    have he : (F x).val = y.val := congrArg
      (fun z : projectiveGradedAway f (fun n ↦ I • W n) ↦ z.val) hx
    exact ⟨x, Subtype.ext he⟩

end SerrePositivity.AlgebraicGeometry
