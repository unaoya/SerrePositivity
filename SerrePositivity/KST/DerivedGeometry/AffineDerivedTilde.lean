module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeExact
public import SerrePositivity.KST.DerivedGeometry.ExactDerivedHomology

/-!
概要：左 H 加群の非有界導来圏から実際の係数 Dqc への tilde を構成する。
方針：完全な係数 tilde を全加群層の導来圏へ降ろし、コホモロジー条件へ制限する。
規約：完全忠実性・本質的全射性を仮定しない。
使われ方：Bondal–van den Bergh Thm 3.1.1、TT §3、Toën §3.2 のアフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w₁ w₂
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory.{w₁} (ModuleCat.{u} H)]
  [HasDerivedCategory.{w₂} (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：左 H 加群の非有界導来圏から全係数加群層の導来圏への tilde。
方針：証明済みの完全な係数 tilde に Mathlib の導来化を適用する。
規約：標的は元の全加群層の導来圏。
使われ方：TT §3、Toën §3.2 の実際の Dqc への比較関手。
-/
def affineDerivedTilde : DerivedCategory (ModuleCat.{u} H) ⥤
    DerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules :=
  (affineCoefficientTildeFunctor (R := R) H).mapDerivedCategory

/--
概要：導来係数 tilde は整数シフトと可換。
方針：完全関手の導来化の標準比較を保持する。
規約：Mathlib のシフト構造を使う。
使われ方：Toën §3.2 のアフィン導来比較の三角構造。
-/
instance affineDerivedTilde_commShift : (affineDerivedTilde (R := R) H).CommShift ℤ :=
  inferInstanceAs ((affineCoefficientTildeFunctor (R := R) H).mapDerivedCategory.CommShift ℤ)

/--
概要：導来係数 tilde は三角関手。
方針：係数 tilde の完全性を使う。
規約：非有界導来圏の標準三角形を保持する。
使われ方：TT §3、Toën §3.2 のアフィン比較。
-/
instance affineDerivedTilde_isTriangulated : (affineDerivedTilde (R := R) H).IsTriangulated :=
  inferInstanceAs ((affineCoefficientTildeFunctor (R := R) H).mapDerivedCategory.IsTriangulated)

/--
概要：導来係数 tilde のコホモロジーは元の H 加群コホモロジーの tilde。
方針：完全関手の一般の導来コホモロジー比較を適用する。
規約：各複体の有界性は要求しない。
使われ方：Toën §3.2 の実際の Dqc への値域判定。
-/
def affineDerivedTildeHomologyIso (n : ℤ) :
    affineDerivedTilde (R := R) H ⋙ DerivedCategory.homologyFunctor
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules n ≅
    DerivedCategory.homologyFunctor (ModuleCat.{u} H) n ⋙ affineCoefficientTildeFunctor (R := R) H :=
  exactFunctorDerivedHomologyIso (affineCoefficientTildeFunctor (R := R) H) n

/--
概要：導来係数 tilde の像は実際の準連接コホモロジー条件を満たす。
方針：全次数のコホモロジー比較と係数 tilde の準連接性を使う。
規約：Dqc を各項準連接な複体の導来圏として定義し直さない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン比較。
-/
lemma affineDerivedTilde_hasQuasicoherentCohomology (M : DerivedCategory (ModuleCat.{u} H)) :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology
      ((affineDerivedTilde (R := R) H).obj M) := by
  intro n
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.mapIso
      ((affineDerivedTildeHomologyIso (R := R) H n).app M)).symm
    (affineCoefficientTildeFunctor_isQuasicoherent H
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} H) n).obj M))

/--
概要：左 H 加群の非有界導来圏から実際の係数 Dqc への比較関手。
方針：導来係数 tilde を準連接コホモロジーの充満部分圏へ制限する。
規約：同値性はアフィンコホモロジーの追加計算の後に証明する。
使われ方：Toën §3.2、KST D4・T1′ のアフィン導来比較。
-/
def affineDerivedTildeToDqc : DerivedCategory (ModuleCat.{u} H) ⥤
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Dqc :=
  ObjectProperty.lift _ (affineDerivedTilde (R := R) H)
    (affineDerivedTilde_hasQuasicoherentCohomology H)

/--
概要：導来係数 tilde は同型を反映する。
方針：完全な層の関手の同型反映を全コホモロジーから導来化する。
規約：導来 Hom の完全忠実性は別の主張。
使われ方：Toën §3.2 のアフィン導来比較の保存性。
-/
instance affineDerivedTilde_reflectsIsomorphisms :
    (affineDerivedTilde (R := R) H).ReflectsIsomorphisms :=
  exactFunctorDerived_reflectsIsomorphisms (affineCoefficientTildeFunctor (R := R) H)

/--
概要：比較関手を全加群層の導来圏へ含めると同じ導来 tilde になる。
方針：対象条件への標準 lift の因子分解を使う。
規約：元の複体の導来像を変更しない。
使われ方：Toën §3.2 のアフィン導来比較の正方形。
-/
def affineDerivedTildeInclusionIso :
    affineDerivedTildeToDqc (R := R) H ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).dqcInclusion ≅
    affineDerivedTilde (R := R) H :=
  Iso.refl _

/--
概要：比較は元の H 加群複体の各項の係数 tilde の導来像と自然同型。
方針：完全関手の導来化の因子分解を保持する。
規約：同じ複体と局所化関手の正方形を明示する。
使われ方：TT §3、Toën §3.2 のアフィン導来比較。
-/
def affineDerivedTildeSquare :
    DerivedCategory.Q ⋙ affineDerivedTilde (R := R) H ≅
    (affineCoefficientTildeFunctor (R := R) H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (affineCoefficientTildeFunctor (R := R) H).mapDerivedCategoryFactors

end SerrePositivity.KST.DerivedGeometry
