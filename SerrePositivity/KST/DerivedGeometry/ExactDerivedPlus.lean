module

public import SerrePositivity.KST.DerivedGeometry.ExactDerivedHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
概要：完全関手の実際の導来化を bounded below 導来圏へ制限する。
方針：全コホモロジーの比較から下限を保存し、充満部分圏へ持ち上げる。
規約：非有界導来化そのものを変更しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の段階的アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w w'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
概要：完全関手の導来化はコホモロジーの下限を保つ。
方針：下限未満のコホモロジーの零を自然比較同型で移す。
規約：複体の各項の下限を要求しない。
使われ方：TT §3、Toën §3.2 の bounded below の導来関手。
-/
lemma exactDerived_isGE (K : DerivedCategory C) (n : ℤ) (hK : K.IsGE n) :
    (F.mapDerivedCategory.obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact (Functor.map_isZero F (hK i hi)).of_iso ((exactFunctorDerivedHomologyIso F i).app K)

/--
概要：完全関手の導来化の bounded below 導来圏への実際の制限。
方針：コホモロジーの下限の保存を使い、元の導来関手を充満部分圏へ持ち上げる。
規約：非有界導来関手との包含による比較は定義的に恒等。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン左導来関手。
-/
def exactDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
    intro K
    obtain ⟨n, hn⟩ := K.property
    exact ⟨n, exactDerived_isGE F K.obj n hn⟩)

/--
概要：bounded below への制限は元の非有界導来関手と自然に可換。
方針：充満部分圏への持ち上げと包含の標準比較を使う。
規約：元の導来関手の像を保持する。
使われ方：TT §3、Toën §3.2 のアフィン比較の段階間の両立。
-/
def exactDerivedFunctorPlusSquare :
    exactDerivedFunctorPlus F ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory := Iso.refl _

/-- 概要：bounded below の完全導来関手はシフトと可換。方針：充満部分圏への持ち上げを使う。
規約：整数シフト。使われ方：TT §3、Toën §3.2 の三角関手。 -/
instance exactDerivedFunctorPlus_commShift : (exactDerivedFunctorPlus F).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

/-- 概要：bounded below の完全導来関手は三角関手。方針：元の導来関手と包含の三角性を使う。
規約：標準の三角構造。使われ方：TT §3、Toën §3.2 のアフィン導来比較。 -/
instance exactDerivedFunctorPlus_isTriangulated : (exactDerivedFunctorPlus F).IsTriangulated := by
  dsimp [exactDerivedFunctorPlus]
  infer_instance

end SerrePositivity.KST.DerivedGeometry
