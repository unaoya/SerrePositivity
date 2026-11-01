module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ExteriorDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ExteriorSequence
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
概要：KST Def3.1 の標準添加を既存の dg 関手の合成として構成する。
方針：係数変更の単位、外積の底変更、零生成加群への射を順に合成する。
規約：目標は係数環上の空 Koszul dg 圏の係数制限。単位・積は各 dg 関手が保存する。
使われ方：通常の普遍チャートへの標準添加の dg 圏としての模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：係数環で d の値が消えるなら生成元微分の底変更は零。
方針：純粋 tensor の微分公式から tensor 帰納法で示す。
規約：KST Def3.1。使われ方：零生成加群への dg 関手の微分条件。 -/
theorem exteriorBaseChangeDifferential_eq_zero (φ : R →+* S) (d : M →ₗ[R] R)
    (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    exteriorBaseChangeDifferential (S := S) d = 0 := by
  let := φ.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s m => simp [hd, RingHom.algebraMap_toAlgebra]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：係数環 S を空 Koszul 一対象 dg 圏として表す対象型。
方針：空の有限生成加群と唯一の関係式族を使う。
規約：KST Def3.1、Hom は S の次数0単一複体と同型。
使われ方：標準添加 dg 関手の目標。 -/
abbrev EmptyKoszulObject (S : Type u) [CommRing S] :=
  ExteriorKoszulObject (Finsupp.linearCombination S (Fin.elim0 : Fin 0 → S))

/-- 概要：係数変更後の外積 dg 圏から空 Koszul dg 圏への生成元を消す関手。
方針：零生成元射と底変更微分の消滅を外積 dg 関手へ渡す。
規約：KST Def3.1。使われ方：標準添加の係数変更後の段階。 -/
def exteriorBaseChangedAugmentationDGFunctor (φ : R →+* S) (d : M →ₗ[R] R)
    (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    DifferentialGraded.DGFunctor S
      (ExteriorKoszulObject (exteriorBaseChangeDifferential (S := S) d))
      (EmptyKoszulObject S) := by
  letI := φ.toAlgebra
  exact exteriorKoszulDGFunctor (0 : S ⊗[R] M →ₗ[S] (Fin 0 →₀ S)) _ _ (by
    rw [LinearMap.comp_zero, exteriorBaseChangeDifferential_eq_zero φ d hd])

/-- 概要：係数代入で微分が消える Koszul dg 圏の標準添加関手。
方針：係数変更の単位と底変更比較と生成元を消す関手を合成する。
規約：KST Def3.1、既存 DGRestriction と DGBaseChange のみを使う。
使われ方：通常の普遍チャートの dg 模型への標準添加。 -/
def exteriorAugmentationDGFunctor (φ : R →+* S) (d : M →ₗ[R] R)
    (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    DifferentialGraded.DGFunctor R (ExteriorKoszulObject d)
      (DifferentialGraded.ScalarExtension.DGRestriction φ (EmptyKoszulObject S)) := by
  letI := φ.toAlgebra
  exact EnrichedFunctor.comp (DifferentialGraded.Complex R)
    (DifferentialGraded.ScalarExtension.unitDGFunctor φ (ExteriorKoszulObject d))
    (DifferentialGraded.ScalarExtension.restrictDGFunctor φ
      (EnrichedFunctor.comp (DifferentialGraded.Complex S)
        (exteriorKoszulBaseChangeDGFunctor φ d)
        (exteriorBaseChangedAugmentationDGFunctor φ d hd)))

end SerrePositivity.KST.DerivedBlowup
