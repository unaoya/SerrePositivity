module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeMultiplication
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST Def3.1 の Koszul dg 圏のスカラー拡大を基底変更後の Koszul dg 圏へ比較する。
方針：構成済み cochain 同型の逆を Hom の写像とし、単位・乗法保存を使う。
規約：既存 TransportEnrichment による DGBaseChange を採用する。
使われ方：チャート dg 代数の底変更と重なりの同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：Koszul 一対象 dg 圏の係数変更から基底変更した生成加群の dg 圏への dg 関手。
方針：外積 cochain 同型の逆と強モノイダル係数変更の単位・乗法比較を使う。
規約：KST Def3.1、平坦性と2の可逆性不要。
使われ方：導来 blowup チャートの dg スカラー拡大比較。 -/
def exteriorKoszulBaseChangeDGFunctor (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    EnrichedFunctor (DifferentialGraded.Complex S)
      (DifferentialGraded.ScalarExtension.DGBaseChange φ (ExteriorKoszulObject d))
      (ExteriorKoszulObject (exteriorBaseChangeDifferential (S := S) d)) := by
  letI := φ.toAlgebra
  exact
    { obj := fun _ => .point
      map := fun _ _ => (exteriorCochainBaseChangeIso φ d).inv
      map_id := fun _ => exteriorCochainBaseChange_unit φ d
      map_comp := fun _ _ _ => exteriorCochainBaseChange_mul φ d }

/-- 概要：Koszul dg 底変更関手の Hom の射は複体同型。
方針：Hom 写像は構成済み cochain 同型の逆である。
規約：KST Def3.1。使われ方：底変更の局所 dg 同値性。 -/
theorem exteriorKoszulBaseChangeDGFunctor_map_isIso (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    ∀ x y, IsIso ((exteriorKoszulBaseChangeDGFunctor φ d).map x y) := by
  let := φ.toAlgebra
  intro x y
  change IsIso (exteriorCochainBaseChangeIso φ d).inv
  infer_instance

/-- 概要：Koszul dg 底変更関手は準同値。
方針：Hom の複体同型と一対象型から H⁰ 上の本質的全射を示す。
規約：KST Def3.1、準同値は既存 QuasiEquivalence を用いる。
使われ方：Koszul チャートの dg スカラー拡大比較。 -/
theorem exteriorKoszulBaseChangeDGFunctor_quasiEquivalence (φ : R →+* S)
    (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    DifferentialGraded.QuasiEquivalence (exteriorKoszulBaseChangeDGFunctor φ d) := by
  let := φ.toAlgebra
  constructor
  · intro x y
    have := exteriorKoszulBaseChangeDGFunctor_map_isIso φ d x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject (exteriorBaseChangeDifferential (S := S) d) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
