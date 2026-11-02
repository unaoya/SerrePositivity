-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.ExcisionDerived（仮。原典 Cor 8.12 と E3 の欄 excision）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.3・§3.2 の 5・6、単位 A6-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.Interface
-- 本ファイルは drafts/A6/{SheafOfSetsExcision,ArcSheafProperty}.lean、drafts/Sheaves/SpaceValued.lean（S8）、drafts/A4/InterfaceFields.lean、
-- drafts/A5/PerfectSiteComparison.lean を import する。

/-!
# excision（BS 著者版 Cor 8.12）と E3 の欄 `excision`

## 概要
S → S′ 離散で導来 p 完備、I ⊂ S 導来 p 完備（S 加群として）、`ArcOutside f I` ⇒ CAlg_R の四角形 S_perfd → S′_perfd、S_perfd → (S/I)_perfd、
S′_perfd → (S′/IS′)_perfd、(S/I)_perfd → (S′/IS′)_perfd は引き戻し。E3 の欄 `excision` はこれ（界面の `ordinarySquare … ≫ perfd`）。

## 方針
A6-3 の集合の層の押し出し F_S = F_{S′} ⊔_{F_{S′/I}} F_{S/I} を S8 で空間値の層の押し出しに持ち上げ（単射に沿う離散の押し出しは離散、
離散な前層の層化は 1 圏の層化）、前層の押し出し P → F_S が局所同値、E 値の層 O（Prop 8.10）は局所同値で局所的なので
Γ(F_S, O) ≃ Γ(P, O) = Γ(F_{S′}, O) ×_{Γ(F_{S′/I}, O)} Γ(F_{S/I}, O)、Γ(F_T, O) = lim_{Perfd_{T/}} O = T_perfd（Prop 8.5）。

## 規約
S・T は完備なので `e3Perfd_of_complete`（A4-3）で S_perfd に読み替える。S/I・T/IT の導来 p 完備性は G-A6-10。CAlg_R の引き戻しは U が反映（G-A5-16）。

## 使われ方
`PerfectoidizationInterfaceCAlg.excision`（A9）。環の帰結は既存（`Perfectoidization/Derived/Excision`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.DerivedCompletion

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 概要：S8 の 6：Γ(F_T, O) := lim_{el(F_T)} O = lim_{Perfd_{T/}} O（F_T の元の圏は Perfd_{T/}）、これは T_perfd（Prop 8.5 の極限の形、A5-1）。
方針：`sectionsOf`（Sheaves/SpaceValued）と `perfectoidization_isLimit`。
規約：CAlg_R。
使われ方：`perfectoidization_excision`。 -/
theorem sectionsOf_homSheaf_eq_perfectoidization (T : Type u) [CommRing T] [Algebra R T] : True := by trivial

/-- 概要：前層の押し出し P := F_{S′} ⊔_{F_{S′/I}} F_{S/I}（点ごとの集合の押し出し、離散）から F_S への射は arc 局所同値（S8 の 2・3 と A6-3 の `homSheaf_pushout`）。
方針：`discretePushout_isDiscrete`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`。
規約：—
使われ方：`perfectoidization_excision`。 -/
theorem homPresheafPushout_localEquiv : True := by trivial

/-- 概要：Cor 8.12：四角形 S_perfd、S′_perfd、(S/I)_perfd、(S′/IS′)_perfd は CAlg_R の引き戻し（S′ は与えられたもの）。
方針：`excision_of_excision_prod`（A6-3）で S′ × S/I に替え、`homPresheafPushout_localEquiv` と S8 の 5（`sections_localEquiv_iso`、O は層：`structurePresheaf_isArcSheaf`）、
S8 の 4（Γ(−, O) は前層の押し出しを引き戻しに）、`sectionsOf_homSheaf_eq_perfectoidization`。引き戻しの射が perfd の関手性の射に一致すること（紙 4）。
規約：D(R) で示し U が反映（G-A5-16）。
使われ方：`e3Excision`。 -/
theorem perfectoidization_excision {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) : True := by trivial

/-- 概要：G-A6-10：S・I が導来 p 完備なら S/I も；T と IT（I の像）についても。
方針：完備加群の短完全列（HA/DerivedCompletion、2b 後の名前）。
規約：—
使われ方：`e3Excision` で商を Def 8.2 の定義域に入れる。 -/
theorem quotient_isModuleComplete : True := by trivial

/-- 概要：E3 の `excision`：`IsPullbackSquare (ordinarySquare R f (quotientProjection R S I) (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I) (quotientSquare_commutes R f I) ≫ e3Perfd p R)`。
方針：`perfectoidization_excision` と `e3Perfd_of_complete`（A4-3、四頂点とも完備：`quotient_isModuleComplete`）。
規約：`PerfectoidizationInterfaceCAlg.excision` の型そのまま。
使われ方：A9。 -/
theorem e3Excision {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) :
    IsPullbackSquare (ordinarySquare R f (quotientProjection R S I)
      (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
      (quotientSquare_commutes R f I) ≫ e3Perfd p R) := by
  sorry -- Cor 8.12（A6-2〜A6-4、S8）を待つ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
