module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing

/-!
# 非単位単体環の実係数射と整数単位化

概要：非単位単体環の全ての面・退化と可換な実準同型を明示する。
方針：各次数の非単位環準同型と自然性を整数単位化へ移す。
規約：KST Proposition 4.14 の非可換再記述。使われ方：実 aI→I の包含。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：非単位単体環の実係数射。
方針：全次数の実環準同型と全単体射の自然性を保持する。
規約：KST Proposition 4.14、追加の H_* の結論を含めない。
使われ方：実係数イデアルの包含と ĜL への実誘導射。 -/
structure NonUnitalSimplicialRingHom (I J : NonUnitalSimplicialRing.{u}) where
  /-- 概要：各次数の実非単位環準同型。方針：実係数写像。
  規約：KST Proposition 4.14。使われ方：実単位化写像の各成分。 -/
  app : ∀ k, I.obj k →ₙ+* J.obj k
  /-- 概要：全ての実面・退化との可換性。方針：実準同型の合成の等式。
  規約：KST Proposition 4.14。使われ方：実単体的射への束ね。 -/
  naturality : ∀ {k l} (f : k ⟶ l), (app l).comp (I.map f) = (J.map f).comp (app k)

/-- 概要：非単位単体環の実係数射を標準整数単位化へ移す実自然変換。
方針：実単位化の合成保存と元の実係数自然性を用いる。
規約：KST Proposition 4.14。使われ方：成分環と ĜL の実係数変更。 -/
def NonUnitalSimplicialRingHom.unitizationMap {I J : NonUnitalSimplicialRing.{u}}
    (f : NonUnitalSimplicialRingHom I J) : I.standardIdeal.ambient ⟶ J.standardIdeal.ambient where
  app k := RingCat.ofHom (integerUnitizationMap (f.app k))
  naturality {k l} φ := by
    apply RingCat.hom_ext
    change (integerUnitizationMap (f.app l)).comp (integerUnitizationMap (I.map φ)) =
      (integerUnitizationMap (J.map φ)).comp (integerUnitizationMap (f.app k))
    rw [← integerUnitizationMap_comp, ← integerUnitizationMap_comp, f.naturality]

end SerrePositivity.KST.ProExcision
