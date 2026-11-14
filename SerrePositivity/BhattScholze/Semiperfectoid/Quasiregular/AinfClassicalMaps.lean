module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.AinfClassical
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift

/-!
# 固定 A_inf の剰余表示と標準持ち上げ

## 概要
証明した固定 A_inf の prism データを選び、perfectoid 環の射を完全 prism の射に持ち上げる。
## 方針
実際の存在定理から選び、既存の Lemma 4.8 の全有界標的への一意持ち上げを使う。
## 規約
BS 著者版 Theorem 3.10・Lemma 4.8・Proposition 7.10。零環も含む。
## 使われ方
A3 の ainfData・ainfPrism・ainfResidueAlgebra・rootBasePrismMap の古典的な部品。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Prismatic _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 固定係数環上で、存在を証明した完全 prism の一つを選ぶ。 -/
def ainfClassicalPrism : OrientedPrism p (ainfClassicalCoefficients p R) :=
  (exists_ainfClassicalPrism p R hR).choose

/-- 選択した prism の δ は、固定した標準 δ 構造。 -/
theorem ainfClassicalPrism_delta :
    (ainfClassicalPrism p R hR).deltaStructure = ainfClassicalDelta p R hR :=
  (exists_ainfClassicalPrism p R hR).choose_spec.1

/-- 選択した A_inf prism は完全。 -/
theorem ainfClassicalPrism_perfect : (ainfClassicalPrism p R hR).deltaStructure.IsPerfect :=
  (exists_ainfClassicalPrism p R hR).choose_spec.2.1

/-- 選択した A_inf prism は有界。 -/
theorem ainfClassicalPrism_bounded : IsBoundedPrism (ainfClassicalPrism p R hR) :=
  (exists_ainfClassicalPrism p R hR).choose_spec.2.2.1

/-- 固定 θ を通す、選択した A_inf の剰余と R の環同型。 -/
def ainfClassicalResidueEquiv :
    ainfClassicalCoefficients p R ⧸ (ainfClassicalPrism p R hR).ideal ≃+* R :=
  (exists_ainfClassicalPrism p R hR).choose_spec.2.2.2.choose

/-- 剰余比較は、元の固定 θ を変えない。 -/
theorem ainfClassicalResidueEquiv_theta : (ainfClassicalResidueEquiv p R hR).toRingHom.comp
    (Ideal.Quotient.mk (ainfClassicalPrism p R hR).ideal) = ainfClassicalTheta p R hR :=
  (exists_ainfClassicalPrism p R hR).choose_spec.2.2.2.choose_spec

/-- R 代数を固定 A_inf の剰余上の代数とみなす。 -/
def ainfClassicalResidueAlgebra (S : Type u) [CommRing S] [Algebra R S] :
    Algebra (ainfClassicalCoefficients p R ⧸ (ainfClassicalPrism p R hR).ideal) S :=
  ((algebraMap R S).comp (ainfClassicalResidueEquiv p R hR).toRingHom).toAlgebra

/-- perfectoid 環の射を、その固定 A_inf の prism の射へ一意性を用いて持ち上げる。 -/
def ainfClassicalMap (S : Type u) [CommRing S] (hS : IsIntegralPerfectoid S p) (f : R →+* S) :
    OrientedPrism.Hom (ainfClassicalPrism p R hR) (ainfClassicalPrism p S hS) :=
  (_root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded (ainfClassicalPrism p R hR)
    (ainfClassicalPrism_perfect p R hR) (ainfClassicalPrism p S hS)
    (ainfClassicalPrism_bounded p S hS)
    ((ainfClassicalResidueEquiv p S hS).symm.toRingHom.comp
      (f.comp (ainfClassicalResidueEquiv p R hR).toRingHom))).choose

/-- A_inf の標準持ち上げは、指定した元の環射を剰余で誘導する。 -/
theorem ainfClassicalMap_quotient (S : Type u) [CommRing S] (hS : IsIntegralPerfectoid S p)
    (f : R →+* S) : (ainfClassicalMap p R hR S hS f).quotientMap =
      (ainfClassicalResidueEquiv p S hS).symm.toRingHom.comp
        (f.comp (ainfClassicalResidueEquiv p R hR).toRingHom) :=
  (_root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded (ainfClassicalPrism p R hR)
    (ainfClassicalPrism_perfect p R hR) (ainfClassicalPrism p S hS)
    (ainfClassicalPrism_bounded p S hS) _).choose_spec.1

/-- 根付き基底への構造射を、固定 A_inf 間の prism 射へ持ち上げる。 -/
def rootFamilyAinfMap (J : Type u) :
    OrientedPrism.Hom (ainfClassicalPrism p R hR)
      (ainfClassicalPrism p (rootFamilyBase p R J) (rootFamilyBase_isIntegralPerfectoid p R J hR)) :=
  ainfClassicalMap p R hR _ (rootFamilyBase_isIntegralPerfectoid p R J hR) (algebraMap R _)

end SerrePositivity.BhattScholze.Semiperfectoid
