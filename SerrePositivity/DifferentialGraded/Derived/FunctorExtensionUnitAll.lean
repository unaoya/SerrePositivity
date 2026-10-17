module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionPerfect
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentableUnit
public import SerrePositivity.DifferentialGraded.Derived.CompactAdjunctionCoproducts
public import SerrePositivity.DifferentialGraded.Endomorphism.IsoLocus
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Hom準同型に沿う導来単位の全加群上の可逆性

## 概要
Hom準同型に沿う導来単位の全加群上の可逆性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedNatTransIsoLocus_stableUnderRetracts
    (G : DerivedModuleCategory A D ⥤ DerivedModuleCategory A D)
    (α : 𝟭 (DerivedModuleCategory A D) ⟶ G) :
    (derivedNatTransIsoLocus A D G α).IsStableUnderRetracts where
  of_retract r hY := by
    exact MorphismProperty.of_retract
      (P := MorphismProperty.isomorphisms (DerivedModuleCategory A D))
      (α.retractArrowApp r) hY

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).Additive := dgDerivedRestriction_additive A D E F
local instance : (dgDerivedExtension A D E F).Additive := dgDerivedExtension_additive A D E F
local instance : NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ :=
  dgDerivedExtensionUnit_commShift A D E F

lemma dgDerivedRestriction_preservesCoproduct {J : Type u} (G : J → DerivedModuleCategory A E) :
    PreservesColimit (Discrete.functor G) (dgDerivedRestriction A D E F) :=
  derivedAdjunction_rightAdjoint_preservesCoproduct A D E
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (dgDerivedExtensionRestrictionAdjunction A D E F) G
    (fun _ hP => dgDerivedExtension_compact A D E F hP)

instance dgDerivedRestriction_preservesCoproductsOfShape (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (dgDerivedRestriction A D E F) where
  preservesColimit {K} := by
    let := dgDerivedRestriction_preservesCoproduct A D E F (K.obj ∘ Discrete.mk)
    exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

lemma dgDerivedExtensionUnit_isIso_onPerfect (hF : HomQuasiIso F)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    IsIso ((dgDerivedExtensionUnit A D E F).app X) := by
  let P := derivedNatTransIsoLocus A D (dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F)
    (dgDerivedExtensionUnit A D E F)
  change P X
  apply ((modulePerfect_le_iff_generators A D P).2 ?_) X hX
  intro d
  exact dgDerivedExtensionUnit_representable_isIso A D E F hF d

/-- Hom準同型性だけで導来単位は全対象で同型。本質的全射性はここでは使わない。 -/
lemma dgDerivedExtensionUnit_isIso_all (hF : HomQuasiIso F) (X : DerivedModuleCategory A D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app X) := by
  let P := derivedNatTransIsoLocus A D (dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F)
    (dgDerivedExtensionUnit A D E F)
  change P X
  apply moduleLocalizing_all A D P
  · intro J G hG
    let := (dgDerivedExtensionRestrictionAdjunction A D E F).leftAdjoint_preservesColimits
    exact derivedNatTransIsoLocus_coproduct A D _ (dgDerivedExtensionUnit A D E F) G hG
  · intro Y hY
    exact dgDerivedExtensionUnit_isIso_onPerfect A D E F hF hY

/-- Hom準同型に沿う導来延長は完全忠実。 -/
def dgDerivedExtensionFullyFaithful (hF : HomQuasiIso F) :
    (dgDerivedExtension A D E F).FullyFaithful := by
  letI (X : DerivedModuleCategory A D) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).unit.app X) :=
    dgDerivedExtensionUnit_isIso_all A D E F hF X
  letI := NatIso.isIso_of_isIso_app (dgDerivedExtensionRestrictionAdjunction A D E F).unit
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).fullyFaithfulLOfIsIsoUnit

end SerrePositivity.DifferentialGraded
