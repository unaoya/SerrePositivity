module

public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingleHomology
public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusBounds

/-!
概要：非輪状な単一対象の bounded below 右導来像は標準 t 構造の心に入る。
方針：同じ下限の injective 模型で下限を保ち、通常の正次数右導来の消滅で上限を得る。
規約：非有界の比較をこの結果だけから主張しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] (X : C)

/--
概要：単一対象の右導来像は負次数のコホモロジーを持たない。
方針：右導来関手の下限保存を適用する。
規約：全ての対象に成り立つ。
使われ方：TT §3、Toën §3.2 の心での導来比較。
-/
instance rightDerivedPlus_single_isGE :
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)).IsGE 0 :=
  rightDerivedPlus_isGE F _ 0

/--
概要：通常の正次数右導来が全て零の対象の bounded below 右導来像は次数零以下。
方針：各正整数次数のコホモロジーを元の injective 分解で計算する。
規約：非輪状性を入力とし、導来比較同型の存在は入力にしない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン非輪状性。
-/
lemma rightDerivedPlus_single_isLE
    (h : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj X)) :
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)).IsLE 0 := by
  apply (DerivedCategory.Plus.isLE_ι_obj_iff _ 0).mp
  apply (DerivedCategory.isLE_iff _ 0).mpr
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := by
    refine ⟨(i - 1).toNat, ?_⟩
    omega
  subst i
  exact rightDerivedPlusSingle_homology_isZero F (injectiveResolution X) n (h n)

end SerrePositivity.KST.DerivedGeometry
