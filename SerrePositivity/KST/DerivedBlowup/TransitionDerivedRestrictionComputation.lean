module

public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence

/-!
概要：KST §3.1 の標準導来制限単位・合成同型を実加群上で計算する。
方針：自然同型の延長の成分公式を使い、主局所化の指定対象と生成射で計算する。
規約：元の加群制限同型の主局所化像と一致することを明示する。
使われ方：加群比較の整合性を導来比較へ移送する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R]
variable {C : Type v} {D : Type w} {E : Type z}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  [Small.{u} C] [Small.{u} D] [Small.{u} E]

/-- 概要：指定導来制限は実加群射の主局所化像で元の制限写像を与える。
方針：主局所化の生成射で構成済み導来制限の持ち上げを計算する。
規約：KST §3.1。使われ方：三重導来比較の中央の射を局所化前へ戻す。 -/
theorem transitionDerivedRestriction_map_Q (F : DGFunctor R C D)
    {M N : ModuleCategory R Dᵒᵖ} (f : M ⟶ N) :
    (dgDerivedRestriction R Cᵒᵖ Dᵒᵖ F.op).map ((moduleToDerived R Dᵒᵖ).map f) =
      (moduleToDerived R Cᵒᵖ).map ((moduleRestriction R Cᵒᵖ Dᵒᵖ F.op.op).map f) := rfl

/-- 概要：標準導来制限単位同型の実加群上の順成分。
方針：延長の成分を局所化前へ戻し、指定因子分解の計算同型を簡約する。
規約：KST §3.1。使われ方：指定導来比較の単位条件の計算。 -/
theorem transitionDerivedRestrictionIdIso_hom_app_Q (F : DGFunctor R C C)
    (h : F = DGFunctor.id C) (M : ModuleCategory R Cᵒᵖ) :
    (transitionDerivedRestrictionIdIso F h).hom.app ((moduleToDerived R Cᵒᵖ).obj M) =
      (moduleToDerived R Cᵒᵖ).map ((transitionRestrictionIdIso F h).hom.app M) := by
  change (moduleDerivedIsoExtension (transitionDerivedRestrictionIdPreIso F h)).hom.app _ = _
  rw [moduleDerivedIsoExtension_hom_app]
  rfl

/-- 概要：標準導来制限単位同型の実加群上の逆成分。
方針：逆方向の延長成分を局所化前へ戻して簡約する。
規約：KST §3.1。使われ方：単位比較を戻す向きでの計算。 -/
theorem transitionDerivedRestrictionIdIso_inv_app_Q (F : DGFunctor R C C)
    (h : F = DGFunctor.id C) (M : ModuleCategory R Cᵒᵖ) :
    (transitionDerivedRestrictionIdIso F h).inv.app ((moduleToDerived R Cᵒᵖ).obj M) =
      (moduleToDerived R Cᵒᵖ).map ((transitionRestrictionIdIso F h).inv.app M) := by
  change (moduleDerivedIsoExtension (transitionDerivedRestrictionIdPreIso F h)).inv.app _ = _
  rw [moduleDerivedIsoExtension_inv_app]
  rfl

/-- 概要：標準導来制限合成同型の実加群上の順成分。
方針：延長の成分を局所化前へ戻し、指定した制限合成同型の生成射を残す。
規約：KST §3.1。使われ方：指定導来比較の三重条件の計算。 -/
theorem transitionDerivedRestrictionCompIso_hom_app_Q (F : DGFunctor R C D)
    (G : DGFunctor R D E) (H : DGFunctor R C E) (h : F.comp G = H)
    (M : ModuleCategory R Eᵒᵖ) :
    (transitionDerivedRestrictionCompIso F G H h).hom.app ((moduleToDerived R Eᵒᵖ).obj M) =
      (moduleToDerived R Cᵒᵖ).map ((transitionRestrictionCompIso F G H h).hom.app M) := by
  change (moduleDerivedIsoExtension (transitionDerivedRestrictionCompPreIso F G H h)).hom.app _ = _
  rw [moduleDerivedIsoExtension_hom_app]
  rfl

/-- 概要：標準導来制限合成同型の実加群上の逆成分。
方針：逆方向の延長成分を局所化前へ戻し、元の合成同型の逆射を残す。
規約：KST §3.1。使われ方：三重比較を戻す向きでの計算。 -/
theorem transitionDerivedRestrictionCompIso_inv_app_Q (F : DGFunctor R C D)
    (G : DGFunctor R D E) (H : DGFunctor R C E) (h : F.comp G = H)
    (M : ModuleCategory R Eᵒᵖ) :
    (transitionDerivedRestrictionCompIso F G H h).inv.app ((moduleToDerived R Eᵒᵖ).obj M) =
      (moduleToDerived R Cᵒᵖ).map ((transitionRestrictionCompIso F G H h).inv.app M) := by
  change (moduleDerivedIsoExtension (transitionDerivedRestrictionCompPreIso F G H h)).inv.app _ = _
  rw [moduleDerivedIsoExtension_inv_app]
  rfl

end SerrePositivity.KST.DerivedBlowup
