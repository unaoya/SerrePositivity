module

public import SerrePositivity.KST.DerivedBlowup.ProjectiveExtensionComparison

/-!
概要：KST §3.1 の代表生成元上の canonical な導来係数拡大比較。
方針：標準分解から通常の代表加群延長同型へ進み、指定随伴で Hom 比較射との一致を示す。
規約：任意同型でなく、構成した同型の随伴像を明示する。
使われ方：構造加群の指定 cartesian 比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R]
variable (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)

/-- 概要：標準分解を介する代表生成元の指定導来係数拡大比較。
方針：通常 graph 延長の代表加群同型を標準分解から持ち上げる。
規約：KST §3.1。使われ方：局所 regular 生成元の canonical な導来係数拡大。 -/
def canonicalRepresentableDerivedExtensionMap (c : C) :
    (dgDerivedExtension R C D F).obj
      ((moduleToDerived R C).obj (ForgetEnrichment.of (Complex R) (representable R c))) ⟶
    (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) (representable R (F.obj c))) :=
  canonicalResolutionExtensionComparison R C D F _ _
    (dgModuleExtensionRepresentableIso R C D F c).hom

/-- 概要：代表生成元の指定導来係数拡大比較は同型。
方針：代表加群のホモトピー射影性と通常の代表延長同型を使う。
規約：KST §3.1。使われ方：cartesian 比較の可逆性を指定経路で導く。 -/
instance canonicalRepresentableDerivedExtensionMap_isIso (c : C) :
    IsIso (canonicalRepresentableDerivedExtensionMap R C D F c) :=
  canonicalResolutionExtensionComparison_isIso R C D F _
    (representable_homotopicallyProjective R C c) _
    (dgModuleExtensionRepresentableIso R C D F c).hom

/-- 概要：代表生成元の指定導来係数拡大同型。
方針：構成済み比較射とその可逆性から同型を読む。
規約：KST §3.1。使われ方：局所 regular 比較との随伴計算。 -/
def canonicalRepresentableDerivedExtensionIso (c : C) :=
  asIso (canonicalRepresentableDerivedExtensionMap R C D F c)

set_option maxHeartbeats 2000000 in
-- graph 随伴の通常単位と代表加群の Hom 比較を照合するために必要。
/-- 概要：指定代表延長同型の随伴像は Hom 写像による代表制限比較の主局所化像。
方針：射影的始域の随伴公式、通常単位の代表加群公式、制限計算同型を使う。
規約：KST §3.1。使われ方：canonical な cartesian 比較との経路の一致。 -/
theorem canonicalRepresentableDerivedExtensionMap_adjunct (c : C) :
    (dgDerivedExtensionRestrictionAdjunction R C D F).homEquiv _ _
      (canonicalRepresentableDerivedExtensionMap R C D F c) =
    (moduleToDerived R C).map (representableRestrictionMap R C D F c) := by
  rw [canonicalRepresentableDerivedExtensionMap,
    canonicalResolutionExtensionComparison_adjunct R C D F _
      (representable_homotopicallyProjective R C c)]
  rw [Adjunction.homEquiv_unit, dgModuleEnrichedRestrictionAdjunction_unit,
    dgModuleRestriction_map]
  change (moduleToDerived R C).map
      (functorExtensionUnit R C D F (representable R c) ≫
        (moduleRestriction R C D F.op).map (dgModuleExtensionRepresentableIso R C D F c).hom) ≫
      (dgDerivedRestrictionComputation R C D F
        (ForgetEnrichment.of (Complex R) (representable R (F.obj c)))).inv = _
  rw [functorExtensionUnit_representable]
  have hc : (dgDerivedRestrictionComputation R C D F
      (ForgetEnrichment.of (Complex R) (representable R (F.obj c)))).inv = 𝟙 _ := by
    simp only [dgDerivedRestrictionComputation, eqToIso.inv]
    rfl
  rw [hc]
  exact Category.comp_id _

end SerrePositivity.KST.DerivedBlowup
