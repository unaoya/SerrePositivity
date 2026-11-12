module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections
public import SerrePositivity.AlgebraicGeometry.GradedScalarComponents

/-!
概要：grading の carrier を保ったまま、指定した基底環の作用を実際の Proj の切断へ移す。
方針：generic な斉次局所化の加群構造と、正次数の標準開の環同型を使う。
規約：元の grading の型 σ は変えず、二つの基底環でも同じ Proj を用いる。
使われ方：動く基底の各段を共通の環へ制限した、自然な Čech の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u v
variable {R S : Type u} {σ : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [SetLike σ S] [AddSubgroupClass σ S] [hR : SMulMemClass σ R S]
variable (G : ℕ → σ) [GradedRing G]

/-- 基底環のスカラーは零次成分に属する。 -/
def gradedOriginalScalarToZero : R →+* G 0 where
  toFun r := ⟨algebraMap R S r, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact SMulMemClass.smul_mem r (SetLike.one_mem_graded G)⟩
  map_one' := Subtype.ext (map_one (algebraMap R S))
  map_mul' r s := Subtype.ext (map_mul (algebraMap R S) r s)
  map_zero' := Subtype.ext (map_zero (algebraMap R S))
  map_add' r s := Subtype.ext (map_add (algebraMap R S) r s)

/-- 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 -/
def gradedOriginalScalarToGlobalSections : R →+* Γ(Proj G, ⊤) :=
  ((Proj G).presheaf.map (eqToHom (Proj.basicOpen_one G).symm).op).hom.comp
    ((Proj.awayToSection G 1).hom.comp
      ((HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))).comp
        (gradedOriginalScalarToZero G)))

/-- 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 -/
theorem gradedOriginalScalarToGlobalSections_restrict {f : S} {d : ℕ}
    (hf : f ∈ G d) (r : R) :
    ((Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
        (gradedOriginalScalarToGlobalSections G r) =
      (Proj.awayToSection G f).hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)
          (gradedOriginalScalarToZero G r)) := by
  have h := congrArg (fun h : CommRingCat.of (HomogeneousLocalization.Away G 1) ⟶
      Γ(Proj G, Proj.basicOpen G f) ↦ h.hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))
          (gradedOriginalScalarToZero G r)))
    (Proj.awayMap_awayToSection G hf (show f = 1 * f from (one_mul f).symm))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  change ((Proj G).presheaf.map (eqToHom (Proj.basicOpen_one G).symm).op ≫
    (Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
      ((Proj.awayToSection G 1).hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))
          (gradedOriginalScalarToZero G r))) = _
  rw [← Functor.map_comp]
  exact h.symm

local instance gradedOriginalProjAwayLocalModule (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  gradedOriginalAwayModule (R := R) G f

/-- 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 -/
theorem gradedOriginalAway_scalar_mul (f : S) (r : R)
    (z : HomogeneousLocalization.Away G f) :
    r • z = HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)
        (gradedOriginalScalarToZero G r) * z := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul]
  change r • z.val = (Localization.mk (algebraMap R S r) (1 : Submonoid.powers f)) * z.val
  rw [Localization.mk_one_eq_algebraMap]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away f)]

/-- 正次数の標準開の構造層の環同型は、元の基底環上でも線形。
空交叉の切断は同一視せず、正次数のチャートだけを扱う。 -/
def gradedOriginalProjAwaySectionLinearEquiv {f : S} {d : ℕ}
    (hf : f ∈ G d) (hd : 0 < d) :
    HomogeneousLocalization.Away G f ≃ₗ[R]
      ((schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections G)).obj
          (op (Proj.basicOpen G f))) :=
  { (Proj.basicOpenIsoAway G f hf hd).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := by
      intro r z
      change (Proj.awayToSection G f).hom (r • z) =
        ((Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
          (gradedOriginalScalarToGlobalSections G r) * (Proj.awayToSection G f).hom z
      rw [gradedOriginalAway_scalar_mul, map_mul,
        gradedOriginalScalarToGlobalSections_restrict G hf r] }

/-- 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 -/
theorem gradedOriginalProjAwaySectionLinearEquiv_pow {f : S} {d : ℕ}
    (hf : f ∈ G d) (hd : 0 < d) (n : ℕ)
    (z : HomogeneousLocalization.Away G f) :
    gradedOriginalProjAwaySectionLinearEquiv G hf hd (z ^ n) =
      @HPow.hPow Γ(Proj G, Proj.basicOpen G f) ℕ Γ(Proj G, Proj.basicOpen G f) inferInstance
        (gradedOriginalProjAwaySectionLinearEquiv G hf hd z) n :=
  map_pow (Proj.awayToSection G f).hom z n

section ScalarComposition
variable {R₀ : Type u} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
variable [IsScalarTower R₀ R S] [hR₀ : SMulMemClass σ R₀ S]

/-- 共通の基底環の大域スカラーは、元の基底環を通る合成と一致する。 -/
theorem gradedOriginalScalarToGlobalSections_comp :
    gradedOriginalScalarToGlobalSections (R := R₀) (hR := hR₀) G =
      (gradedOriginalScalarToGlobalSections (R := R) (hR := hR) G).comp (algebraMap R₀ R) := by
  ext r
  have h0 : gradedOriginalScalarToZero (R := R₀) (hR := hR₀) G r =
      gradedOriginalScalarToZero (R := R) (hR := hR) G (algebraMap R₀ R r) := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply R₀ R S r
  simp only [gradedOriginalScalarToGlobalSections, RingHom.comp_apply]
  rw [h0]

end ScalarComposition
end SerrePositivity.AlgebraicGeometry
