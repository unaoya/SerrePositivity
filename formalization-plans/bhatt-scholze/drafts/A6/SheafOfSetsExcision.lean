-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.SheafOfSetsExcision（仮。原典 Cor 8.12 の証明の集合の層の部分）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §3.2 の 1〜4、単位 A6-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
-- 本ファイルは drafts/A6/{ArcSite,ArcSheafProperty}.lean、drafts/A5/PerfectSiteComparison.lean を import する。

/-!
# 集合の層の excision（BS 著者版 Cor 8.12 の証明の 1 圏の部分）

## 概要
S → S′ を p 完備環の射、I ⊂ S を p 完備なイデアル、`ArcOutside f I`（I を殺さない V への S → V は S′ → V に一意に延びる）とする。
(1) S → S′ × S/I は arc 被覆。(2) perfd は有限積を保つ（G-A6-2）ので S′ を S′ × S/I に替えてよい。(3) 任意の集合の arc 層 F
（affCompl_κ 上。affPerfd_κ 上の層から `sheafEquiv` で延長したもの）について F(S) = F(S′) ×_{F(S′/I)} F(S/I)。(4) 同値な形：
F_S は集合の層の圏で F_{S′} ⊔_{F_{S′/I}} F_{S/I}（F_T := Hom(T, −)）。

## 方針
(3) は原典の "unraveling"：S → S′ に沿う降下 F(S) = eq(F(S′) ⇉ F(S′ ⊗̂_S S′))、S′ ⊗̂_S S′ → S′ × (S′/I ⊗̂_{S/I} S′/I) が arc 被覆（`ArcOutside` の一意性）
なので F(S′ ⊗̂ S′) ↪ F(S′) × F(S′/I ⊗̂ S′/I)、乗法成分は自明、mod I 成分で x̄ ∈ eq(F(S′/I) ⇉ F(S′/I ⊗̂ S′/I)) = F(S/I)（S/I → S′/I は分裂 arc 被覆）。
すべて Mathlib の 1 圏の層（`Presheaf.IsSheaf`、等化子）。

## 規約
S′ は (2) の後は S′ × S/I。完備テンソルは p 完備。κ は全部の環を含むように取る。

## 使われ方
A6-4（S8 で空間値の層・E 値の層へ持ち上げる）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (κ : Cardinal.{u})

/-! ## (1) 被覆 -/

/-- 概要：`ArcOutside f I` なら S → S′ × S/I は arc 被覆（W = V でよい：I ↦ 0 なら S/I を通り、そうでなければ S′ → V に延びる）。
方針：定義の展開。
規約：`IsArcCoverFamily` の二元族 {S → S′, S → S/I}。
使われ方：(3) の降下。 -/
theorem isArcCover_of_arcOutside {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) (h : ArcOutside R p f I) : True := by trivial

/-- 概要：G-A6-9：S → S′ が (1) の形のとき S′ ⊗̂_S S′ → S′ × (S′/I ⊗̂_{S/I} S′/I)（乗法と mod I）は arc 被覆；S/I → S′/I は分裂なので arc 被覆。
方針：S′ ⊗̂_S S′ → V で I ↦ 0 なら第二成分、そうでなければ `ArcOutside` の一意性で二つの S′ → V が一致し乗法を通る。
規約：—
使われ方：(3)。 -/
theorem isArcCover_diagonal_of_arcOutside : True := by trivial
theorem isArcCover_quotient_split : True := by trivial

/-! ## (2) perfd は有限積を保つ -/

/-- 概要：perfectoid 環 T の冪等元 e について eT は perfectoid；perfectoid 環 T と S′ × S″ → T は T = T′ × T″ に分解し、Perfd_{(S′×S″)/} ≅ Perfd_{S′/} × Perfd_{S″/}。
方針：冪等元の分解、`IsIntegralPerfectoid` の成分ごとの判定。
規約：—
使われ方：`perfectoidization_prod`。 -/
theorem perfectoid_factor_of_idempotent : True := by trivial
def perfdUnderProdEquiv : True := trivial

/-- 概要：G-A6-2：(S′ × S″)_perfd ≃ S′_perfd × S″_perfd（CAlg_R、D(R)）。
方針：Prop 8.5 の極限の形（A5-1 `perfectoidization_isLimit_u`）と `perfdUnderProdEquiv`：積圏上の (T′, T″) ↦ T′ × T″ の極限は極限の積。
規約：—
使われ方：Cor 8.12 で S′ を S′ × S/I に替えて戻す（D58）。 -/
theorem perfectoidization_prod : True := by trivial

/-- 概要：S″ := S′ × S/I の四角形（S → S″、I）が引き戻しなら、S′ の四角形も引き戻し（S″/IS″ = S′/IS′ × S/I）。
方針（W9-II-19 で訂正）：左上の S_perfd は積に変わらないので「S′ の四角形と恒等四角形の文字どおりの積」ではない。B := S′_perfd、C := (S/I)_perfd、
D := (S′/IS′)_perfd、g : B → D と書き、`perfectoidization_prod` で S″_perfd ≃ B × C、(S″/IS″)_perfd ≃ D × C。S″ の四角形の引き戻しは
(B × C) ×_{D × C} C（C → D × C は (g, id_C)）で、有限極限の計算により B ×_D C に標準的に同値、各射影は元の商写像と両立する。結論は変わらない。
規約：—
使われ方：Cor 8.12 の帰着。 -/
theorem excision_of_excision_prod : True := by trivial

/-! ## (3)(4) 集合の層の等式 -/

/-- 概要：affPerfd_κ 上の集合の arc 層 F を affCompl_κ へ延長（Mathlib `IsCoverDense.sheafEquiv` の逆、右 Kan 延長）。F(T) = lim_{Perfd_{T/}} F。
方針：`affPerfdInclusion_isCoverDense`（A6-1）。
規約：G-A6-8。
使われ方：以下。 -/
def extendArcSheaf : True := trivial

/-- 概要：(3)：集合の arc 層 F（affCompl_κ 上）、S → S′ が (1) の形なら F(S) ≅ F(S′) ×_{F(S′/I)} F(S/I)。
方針：降下 F(S) = eq(F(S′) ⇉ F(S′ ⊗̂_S S′))、`isArcCover_diagonal_of_arcOutside` で F(S′ ⊗̂ S′) ↪ F(S′) × F(S′/I ⊗̂ S′/I)、成分ごとに読む、
`isArcCover_quotient_split` で eq(F(S′/I) ⇉ F(S′/I ⊗̂ S′/I)) = F(S/I)、分離性で F(S/I) ↪ F(S′/I)。
規約：集合の引き戻し。
使われ方：(4)。 -/
theorem sheafOfSets_excision : True := by trivial

/-- 概要：F_T := Hom(T, −)（affPerfd_κ 上の集合の前層、Prop 8.10 後半で層）。Hom(F_T, F) = F(T)（Yoneda、延長の定義）。
方針：Mathlib の Yoneda と `extendArcSheaf`。
規約：—
使われ方：(4)。 -/
def homSheaf (T : Type u) [CommRing T] : True := trivial
theorem hom_homSheaf_eq : True := by trivial

/-- 概要：(4)：F_S は集合の層の圏で押し出し F_{S′} ⊔_{F_{S′/I}} F_{S/I}（(3) と Yoneda）。F_{S′/I} → F_{S′} は単射。
方針：`sheafOfSets_excision`、`hom_homSheaf_eq`。
規約：Mathlib `Sheaf` の押し出し（`presheafToSheaf` の像）。
使われ方：A6-4（S8 で持ち上げ）。 -/
theorem homSheaf_pushout : True := by trivial
theorem homSheaf_quotient_mono : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
