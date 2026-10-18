module

public import SerrePositivity.KST.DerivedBlowup.ExteriorMapLaws

/-!
概要：KST Def3.1 の Koszul 生成元変換を既存の豊穣関手として構成する。
方針：Koszul cochain map と単位・乗法保存を使う。
規約：始域・終域の対象型に微分を保持して dg 構造を区別する。
使われ方：導来 blowup のチャートと例外因子の遷移。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M N : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 概要：微分を保つ生成元変換が誘導する一対象 dg 関手。
方針：underlying cochain map の単位保存と乗法保存を豊穣関手へ渡す。
規約：KST Def3.1。使われ方：チャート遷移の dg 関手。 -/
def exteriorKoszulDGFunctor (f : M →ₗ[R] N)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (h : dN.comp f = dM) :
    EnrichedFunctor (DifferentialGraded.Complex R)
      (ExteriorKoszulObject dM) (ExteriorKoszulObject dN) where
  obj _ := .point
  map _ _ := exteriorKoszulCochainMap f dM dN h
  map_id _ := exteriorKoszulCochainMap_unit f dM dN h
  map_comp _ _ _ := exteriorKoszulCochainMap_mul f dM dN h

/-- 概要：Koszul dg 関手の Hom 上の射は指定した cochain map。
方針：豊穣関手の定義を展開する。
規約：KST Def3.1。使われ方：基底変換の cocycle と逆写像の比較。 -/
theorem exteriorKoszulDGFunctor_map (f : M →ₗ[R] N)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (h : dN.comp f = dM) :
    (exteriorKoszulDGFunctor f dM dN h).map .point .point =
      exteriorKoszulCochainMap f dM dN h := rfl

end SerrePositivity.KST.DerivedBlowup
