module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedTilde
public import SerrePositivity.KST.DerivedGeometry.AffineTildeAdjunctionExact
public import SerrePositivity.KST.DerivedGeometry.UnboundedDerivedAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules

/-!
概要：実際の全係数加群層の非有界導来圏における tilde と右導来大域切断の随伴。
方針：構成済みの非有界 K-injective 分解と完全な通常 tilde の随伴を使う。
規約：Dqc を各項準連接な複体の導来圏に置き換えない。
使われ方：TT §3・§8、Toën §3.2、BvdB Thm 3.1.1 の実際のアフィン Dqc 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory.{v₁} (ModuleCat.{u} H)]
  [HasDerivedCategory.{v₂} (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：元の全係数加群層の非有界右導来大域切断。
方針：通常の係数大域切断を、証明済みの非有界 K-injective 模型で右導来化する。
規約：H の可換性・平坦性・複体の有界性は不要。
使われ方：TT §3、Toën §3.2 のアフィン係数 Dqc 比較。
-/
def affineDerivedΓ :
    DerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules ⥤
      DerivedCategory (ModuleCat.{u} H) :=
  unboundedRightDerivedFunctor (affineCoefficientΓ (R := R) H)

/--
概要：実際の非有界係数 tilde は右導来大域切断の左随伴。
方針：完全左随伴と加法的右随伴の証明済みの非有界導来随伴を適用する。
規約：単位・余単位の同型性と Dqc 同値は後で証明する。
使われ方：TT §3・§8、Toën §3.2、BvdB Thm 3.1.1 の非有界アフィン比較。
-/
def affineDerivedAdjunction : affineDerivedTilde (R := R) H ⊣ affineDerivedΓ (R := R) H :=
  unboundedDerivedAdjunction (affineCoefficientTildeAdjunction (R := R) H)

end SerrePositivity.KST.DerivedGeometry
