module

public import SerrePositivity.KST.DerivedBlowup.ExteriorComplexMap

/-!
概要：KST Def3.1 の可逆基底変換から整数次数の Koszul 複体の同型を構成する。
方針：線形同型と逆写像の外積を各次数で取り、微分適合性を使う。
規約：同一可換基底環上。微分の同定はデータではなく証明を要求する。
使われ方：チャート重なりと例外因子の Koszul 表示の同型。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R]
  {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 概要：可逆基底変換に対する微分適合性を逆写像へ移す。
方針：適合性を逆写像の像で評価する。規約：KST Def3.1。
使われ方：Koszul 複体の逆 chain map の構成。 -/
theorem exteriorDifferential_inverse (e : M ≃ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp e.toLinearMap = dM) : dM.comp e.symm.toLinearMap = dN := by
  ext n
  have hm := LinearMap.congr_fun h (e.symm n)
  simpa using hm.symm

/-- 概要：微分適合的な線形同型から外積 Koszul chain 複体の同型を作る。
方針：両側の外積 chain map を逆に持ち、各次数で線形同型の逆元律を使う。
規約：KST Def3.1、任意の可換基底環。使われ方：チャートの可逆 Koszul 基底変換。 -/
def exteriorKoszulChainIso (e : M ≃ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp e.toLinearMap = dM) : exteriorKoszulChain dM ≅ exteriorKoszulChain dN where
  hom := exteriorKoszulChainMap e.toLinearMap dM dN h
  inv := exteriorKoszulChainMap e.symm.toLinearMap dN dM (exteriorDifferential_inverse e dM dN h)
  hom_inv_id := by
    ext n z
    apply Subtype.ext
    change ExteriorAlgebra.map e.symm.toLinearMap (ExteriorAlgebra.map e.toLinearMap z.val) = z.val
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext; simp
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, he]
    exact AlgHom.congr_fun ExteriorAlgebra.map_id z.val
  inv_hom_id := by
    ext n z
    apply Subtype.ext
    change ExteriorAlgebra.map e.toLinearMap (ExteriorAlgebra.map e.symm.toLinearMap z.val) = z.val
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, he]
    exact AlgHom.congr_fun ExteriorAlgebra.map_id z.val

/-- 概要：可逆基底変換を整数 cochain 規約の同型へ延長する。
方針：n↦−n の零延長関手で chain 同型を写す。
規約：KST Def3.1、次数の符号はここで固定。
使われ方：既存の反復 cone 模型と比較するチャートの cochain 同型。 -/
def exteriorKoszulCochainIso (e : M ≃ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp e.toLinearMap = dM) : exteriorKoszulCochain dM ≅ exteriorKoszulCochain dN :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{max u v} R)).mapIso
    (exteriorKoszulChainIso e dM dN h)

end SerrePositivity.KST.DerivedBlowup
