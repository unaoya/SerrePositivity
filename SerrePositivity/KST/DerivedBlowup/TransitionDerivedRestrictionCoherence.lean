module

public import SerrePositivity.KST.DerivedBlowup.TransitionRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：KST §3.1 の dg 遷移に沿う導来加群制限の単位・合成比較。
方針：指定の加群制限同型を主局所化の自然変換延長で送る。
規約：延長の成分は局所化前の加群上で指定経路と一致する。
使われ方：canonical な導来比較の包含鎖に沿う整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z t s

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：主導来局所化前の自然同型を局所化上へ延長する。
方針：順逆の自然変換をそれぞれ延長し、対象の保持する加群で逆元律を確認する。
規約：KST §3.1。使われ方：標準制限の単位・合成比較の導来化。 -/
def moduleDerivedIsoExtension {C : Type v} [DGCategory R C] [Small.{u} C]
    {B : Type t} [Category.{s} B] {F G : DerivedModuleCategory R C ⥤ B}
    (e : moduleToDerived R C ⋙ F ≅ moduleToDerived R C ⋙ G) : F ≅ G where
  hom := Localization.Construction.natTransExtension e.hom
  inv := Localization.Construction.natTransExtension e.inv
  hom_inv_id := by
    apply moduleDerivedNatTrans_ext R C
    intro M
    simpa only [NatTrans.comp_app, NatTrans.id_app, Functor.comp_obj,
      Localization.Construction.natTransExtension_app,
      Localization.Construction.NatTransExtension.app_eq] using
      congrArg (fun τ => τ.app M) e.hom_inv_id
  inv_hom_id := by
    apply moduleDerivedNatTrans_ext R C
    intro M
    simpa only [NatTrans.comp_app, NatTrans.id_app, Functor.comp_obj,
      Localization.Construction.natTransExtension_app,
      Localization.Construction.NatTransExtension.app_eq] using
      congrArg (fun τ => τ.app M) e.inv_hom_id

/-- 概要：延長した自然同型の順成分は局所化前の指定成分。
方針：主局所化の自然変換延長の標準成分公式を使う。
規約：KST §3.1。使われ方：導来比較の計算経路を照合する。 -/
theorem moduleDerivedIsoExtension_hom_app {C : Type v} [DGCategory R C] [Small.{u} C]
    {B : Type t} [Category.{s} B] {F G : DerivedModuleCategory R C ⥤ B}
    (e : moduleToDerived R C ⋙ F ≅ moduleToDerived R C ⋙ G) (M : ModuleCategory R C) :
    (moduleDerivedIsoExtension e).hom.app ((moduleToDerived R C).obj M) = e.hom.app M :=
  Localization.Construction.NatTransExtension.app_eq e.hom M

/-- 概要：延長した自然同型の逆成分も局所化前の指定成分。
方針：逆自然変換の延長の標準成分公式を使う。
規約：KST §3.1。使われ方：標準比較を戻す向きで計算する。 -/
theorem moduleDerivedIsoExtension_inv_app {C : Type v} [DGCategory R C] [Small.{u} C]
    {B : Type t} [Category.{s} B] {F G : DerivedModuleCategory R C ⥤ B}
    (e : moduleToDerived R C ⋙ F ≅ moduleToDerived R C ⋙ G) (M : ModuleCategory R C) :
    (moduleDerivedIsoExtension e).inv.app ((moduleToDerived R C).obj M) = e.inv.app M :=
  Localization.Construction.NatTransExtension.app_eq e.inv M

variable {C : Type v} {D : Type w} {E : Type z}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  [Small.{u} C] [Small.{u} D] [Small.{u} E]

/-- 概要：指定恒等遷移の導来制限の単位同型の局所化前の経路。
方針：導来制限の計算同型に元の加群制限の単位同型を続ける。
規約：KST §3.1。使われ方：導来単位同型の指定。 -/
def transitionDerivedRestrictionIdPreIso (F : DGFunctor R C C) (h : F = DGFunctor.id C) :
    moduleToDerived R Cᵒᵖ ⋙ dgDerivedRestriction R Cᵒᵖ Cᵒᵖ F.op ≅
      moduleToDerived R Cᵒᵖ ⋙ 𝟭 _ :=
  eqToIso (dgDerivedRestriction_fac R Cᵒᵖ Cᵒᵖ F.op) ≪≫
    isoWhiskerRight (transitionRestrictionIdIso F h) (moduleToDerived R Cᵒᵖ)

/-- 概要：指定恒等遷移に沿う導来制限の単位同型。
方針：局所化前の指定経路を自然同型の延長で送る。
規約：KST §3.1。使われ方：canonical な導来比較の単位条件。 -/
def transitionDerivedRestrictionIdIso (F : DGFunctor R C C) (h : F = DGFunctor.id C) :
    dgDerivedRestriction R Cᵒᵖ Cᵒᵖ F.op ≅ 𝟭 _ :=
  moduleDerivedIsoExtension (transitionDerivedRestrictionIdPreIso F h)

/-- 概要：導来制限の二段と直接制限の合成比較の局所化前の経路。
方針：二つの計算同型で加群制限へ戻し、指定合成同型を送り、直接計算同型で戻る。
規約：KST §3.1。使われ方：導来合成同型を選択なしの指定経路に固定する。 -/
def transitionDerivedRestrictionCompPreIso (F : DGFunctor R C D) (G : DGFunctor R D E)
    (H : DGFunctor R C E) (h : F.comp G = H) :
    moduleToDerived R Eᵒᵖ ⋙
        dgDerivedRestriction R Dᵒᵖ Eᵒᵖ G.op ⋙ dgDerivedRestriction R Cᵒᵖ Dᵒᵖ F.op ≅
      moduleToDerived R Eᵒᵖ ⋙ dgDerivedRestriction R Cᵒᵖ Eᵒᵖ H.op :=
  isoWhiskerRight (eqToIso (dgDerivedRestriction_fac R Dᵒᵖ Eᵒᵖ G.op))
      (dgDerivedRestriction R Cᵒᵖ Dᵒᵖ F.op) ≪≫
    isoWhiskerLeft (moduleRestriction R Dᵒᵖ Eᵒᵖ G.op.op)
      (eqToIso (dgDerivedRestriction_fac R Cᵒᵖ Dᵒᵖ F.op)) ≪≫
    isoWhiskerRight (transitionRestrictionCompIso F G H h) (moduleToDerived R Cᵒᵖ) ≪≫
    (eqToIso (dgDerivedRestriction_fac R Cᵒᵖ Eᵒᵖ H.op)).symm

/-- 概要：指定合成 dg 遷移に沿う導来制限の標準合成同型。
方針：局所化前の計算経路を順逆の自然変換として延長する。
規約：KST §3.1。使われ方：導来制限比較の三重条件の行先を揃える。 -/
def transitionDerivedRestrictionCompIso (F : DGFunctor R C D) (G : DGFunctor R D E)
    (H : DGFunctor R C E) (h : F.comp G = H) :
    dgDerivedRestriction R Dᵒᵖ Eᵒᵖ G.op ⋙ dgDerivedRestriction R Cᵒᵖ Dᵒᵖ F.op ≅
      dgDerivedRestriction R Cᵒᵖ Eᵒᵖ H.op :=
  moduleDerivedIsoExtension (transitionDerivedRestrictionCompPreIso F G H h)

end SerrePositivity.KST.DerivedBlowup
