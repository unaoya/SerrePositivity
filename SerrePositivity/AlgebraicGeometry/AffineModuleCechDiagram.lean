module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：アフィン標準被覆の各有限交叉の局所化加群から Čech の係数図式を作る。
方針：分母の積の整除関係に、既存の局所化の制限写像を適用する。
規約：被覆の元が単位イデアルを生成するという仮定は、完全性を示す段で加える。
使われ方：共通アフィン細分の二重 Čech 図式の行・列の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped BigOperators
universe u
variable {A : Type u} [CommRing A] {ι : Type} [DecidableEq ι]
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- 二つの分母が互いに整除するときの局所化加群の同型。 -/
def affineModuleAwayRestrictionIso {a b : A} (hab : a ∣ b) (hba : b ∣ a) :
    ModuleCat.of A (LocalizedModule (Submonoid.powers a) M) ≅
      ModuleCat.of A (LocalizedModule (Submonoid.powers b) M) where
  hom := ModuleCat.ofHom (projectiveModuleAwayRestriction hab)
  inv := ModuleCat.ofHom (projectiveModuleAwayRestriction hba)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    change (projectiveModuleAwayRestriction (M := M) hba).comp
      (projectiveModuleAwayRestriction hab) = LinearMap.id
    rw [projectiveModuleAwayRestriction_comp]
    exact projectiveModuleAwayRestriction_refl a
  inv_hom_id := by
    apply ModuleCat.hom_ext
    change (projectiveModuleAwayRestriction (M := M) hab).comp
      (projectiveModuleAwayRestriction hba) = LinearMap.id
    rw [projectiveModuleAwayRestriction_comp]
    exact projectiveModuleAwayRestriction_refl b

variable (f : ι → A)

/-- 有限交叉を定める被覆元の積。 -/
def affineCechDenominator (T : Finset ι) : A := ∏ i ∈ T, f i

/-- 添字を増やすと、交叉の分母は元の分母の倍数になる。 -/
theorem affineCechDenominator_dvd {T U : Finset ι} (h : T ⊆ U) :
    affineCechDenominator f T ∣ affineCechDenominator f U :=
  Finset.prod_dvd_prod_of_subset T U f h

/-- アフィン標準被覆の各有限交叉での局所化加群の図式。 -/
def affineModuleCechDiagram : Finset ι ⥤ ModuleCat.{u} A where
  obj T := ModuleCat.of A (LocalizedModule (Submonoid.powers (affineCechDenominator f T)) M)
  map h := ModuleCat.ofHom (projectiveModuleAwayRestriction
    (affineCechDenominator_dvd f (leOfHom h)))
  map_id T := by
    apply ModuleCat.hom_ext
    exact projectiveModuleAwayRestriction_refl (affineCechDenominator f T)
  map_comp α β := by
    apply ModuleCat.hom_ext
    exact (projectiveModuleAwayRestriction_comp
      (affineCechDenominator_dvd f (leOfHom α))
      (affineCechDenominator_dvd f (leOfHom β))).symm

/-- 単元の被覆元を追加しても、交叉の分母は元の分母を割る。 -/
theorem affineCechDenominator_insert_dvd (v : ι) (hv : IsUnit (f v)) (T : Finset ι) :
    affineCechDenominator f (insert v T) ∣ affineCechDenominator f T := by
  by_cases h : v ∈ T
  · simpa only [Finset.insert_eq_of_mem h] using (dvd_refl (affineCechDenominator f T))
  · obtain ⟨a, ha⟩ := hv
    refine ⟨(↑(a⁻¹) : A), ?_⟩
    simp only [affineCechDenominator, Finset.prod_insert h, ← ha]
    rw [mul_comm (a : A) (∏ i ∈ T, f i), mul_assoc, a.mul_inv, mul_one]

/-- 被覆元が単元なら、それを交叉へ追加する制限は同型。 -/
theorem affineModuleCechDiagram_map_insert_isIso (v : ι) (hv : IsUnit (f v)) (T : Finset ι) :
    IsIso ((affineModuleCechDiagram M f).map (homOfLE (Finset.subset_insert v T))) := by
  exact (affineModuleAwayRestrictionIso M
    (affineCechDenominator_dvd f (Finset.subset_insert v T))
    (affineCechDenominator_insert_dvd f v hv T)).isIso_hom

end SerrePositivity.AlgebraicGeometry
