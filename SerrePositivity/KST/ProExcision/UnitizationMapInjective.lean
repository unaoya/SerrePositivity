module
public import SerrePositivity.KST.ProExcision.NonUnitalAffineMaps

/-!
# 実係数射の単射性と実単位化・ベクトル群

概要：実非単位環射の単射性を標準単位化と実核イデアル内のベクトルに移す。
方針：第一・第二成分と実ベクトルの各成分を評価する。
規約：KST Proposition 4.14。使われ方：実包含を用いた同変性の反映。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：実非単位環射が単射なら標準整数単位化の実射も単射。
方針：整数成分は保たれ、第二成分には元の単射性を使う。
規約：KST Proposition 4.14。使われ方：実係数包含の像での計算の反映。 -/
lemma integerUnitizationMap_injective {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) (hf : Function.Injective f) :
    Function.Injective (integerUnitizationMap f) := by
  intro x y h
  apply Unitization.ext
  · have he := congrArg (fun z : Unitization ℤ J ↦ z.fst) h
    simpa only [integerUnitizationMap_fst] using he
  · apply hf
    have he := congrArg (fun z : Unitization ℤ J ↦ z.snd) h
    simpa only [integerUnitizationMap_snd] using he

/-- 概要：次数ごとに単射な実係数射は実核イデアル内のベクトル群でも単射。
方針：各成分を周囲の実単位化へ忘れ、実単位化の単射性を使う。
規約：KST Proposition 4.14。使われ方：実アフィン射の同変性の反映。 -/
lemma NonUnitalSimplicialRingHom.columnGroupMap_injective
    {I J : NonUnitalSimplicialRing.{u}} (f : NonUnitalSimplicialRingHom I J)
    (hf : ∀ k, Function.Injective (f.app k)) (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((f.columnGroupMap n).app k).hom := by
  intro v w h
  change v.toAdd = w.toAdd
  funext i
  apply Subtype.ext
  apply integerUnitizationMap_injective (f.app k) (hf k)
  exact congrArg (fun z : Multiplicative (Fin n → J.standardIdeal.ideal k) ↦ (z.toAdd i).val) h

end SerrePositivity.KST.ProExcision
