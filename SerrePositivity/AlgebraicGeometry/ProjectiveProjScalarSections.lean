module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjStandardSections
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech

/-!
概要：次数零の局所化と Proj の構造層との比較を、元の基底環上で扱う。
方針：基底環を零次成分へ送り、分母 1 のチャートから大域スカラーを作る。
規約：零次成分が Proj の大域切断全体であるとは仮定しない。
使われ方：射影 Čech 計算の、共通アフィン細分への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (G : ℕ → Submodule R S) [GradedRing G]

/-- 基底環のスカラーは零次成分に属する。 -/
def projectiveScalarToZero : R →+* G 0 where
  toFun r := ⟨algebraMap R S r, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (G 0).smul_mem r (SetLike.one_mem_graded G)⟩
  map_one' := Subtype.ext (map_one (algebraMap R S))
  map_mul' r s := Subtype.ext (map_mul (algebraMap R S) r s)
  map_zero' := Subtype.ext (map_zero (algebraMap R S))
  map_add' r s := Subtype.ext (map_add (algebraMap R S) r s)

/-- 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 -/
def projectiveScalarToGlobalSections : R →+* Γ(Proj G, ⊤) :=
  ((Proj G).presheaf.map (eqToHom (Proj.basicOpen_one G).symm).op).hom.comp
    ((Proj.awayToSection G 1).hom.comp
      ((HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))).comp
        (projectiveScalarToZero G)))

/-- 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 -/
theorem projectiveScalarToGlobalSections_restrict {f : S} {d : ℕ}
    (hf : f ∈ G d) (r : R) :
    ((Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
        (projectiveScalarToGlobalSections G r) =
      (Proj.awayToSection G f).hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)
          (projectiveScalarToZero G r)) := by
  have h := congrArg (fun h : CommRingCat.of (HomogeneousLocalization.Away G 1) ⟶
      Γ(Proj G, Proj.basicOpen G f) ↦ h.hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))
          (projectiveScalarToZero G r)))
    (Proj.awayMap_awayToSection G hf (show f = 1 * f from (one_mul f).symm))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  change ((Proj G).presheaf.map (eqToHom (Proj.basicOpen_one G).symm).op ≫
    (Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
      ((Proj.awayToSection G 1).hom
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (1 : S))
          (projectiveScalarToZero G r))) = _
  rw [← Functor.map_comp]
  exact h.symm

local instance (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayModule G f

/-- 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 -/
theorem projectiveHomogeneousAway_scalar_mul (f : S) (r : R)
    (z : HomogeneousLocalization.Away G f) :
    r • z = HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)
        (projectiveScalarToZero G r) * z := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul]
  change r • z.val = (Localization.mk (algebraMap R S r) (1 : Submonoid.powers f)) * z.val
  rw [Localization.mk_one_eq_algebraMap]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away f)]

/-- 正次数の標準開の構造層の環同型は、元の基底環上でも線形。
空交叉の切断は同一視せず、正次数のチャートだけを扱う。 -/
def projectiveProjAwaySectionLinearEquiv {f : S} {d : ℕ}
    (hf : f ∈ G d) (hd : 0 < d) :
    HomogeneousLocalization.Away G f ≃ₗ[R]
      ((schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G)).obj
          (op (Proj.basicOpen G f))) :=
  { (Proj.basicOpenIsoAway G f hf hd).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := by
      intro r z
      change (Proj.awayToSection G f).hom (r • z) =
        ((Proj G).presheaf.map (homOfLE (show Proj.basicOpen G f ≤ ⊤ from le_top)).op).hom
          (projectiveScalarToGlobalSections G r) * (Proj.awayToSection G f).hom z
      rw [projectiveHomogeneousAway_scalar_mul, map_mul,
        projectiveScalarToGlobalSections_restrict G hf r] }

/-- 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 -/
theorem projectiveProjAwaySectionLinearEquiv_pow {f : S} {d : ℕ}
    (hf : f ∈ G d) (hd : 0 < d) (n : ℕ)
    (z : HomogeneousLocalization.Away G f) :
    projectiveProjAwaySectionLinearEquiv G hf hd (z ^ n) =
      @HPow.hPow Γ(Proj G, Proj.basicOpen G f) ℕ Γ(Proj G, Proj.basicOpen G f) inferInstance
        (projectiveProjAwaySectionLinearEquiv G hf hd z) n :=
  map_pow (Proj.awayToSection G f).hom z n

end SerrePositivity.AlgebraicGeometry
