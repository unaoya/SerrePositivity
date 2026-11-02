-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.SpaceValued（仮。S8。Sheaves/ の続きか別層かは調整役）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.4、S8。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.F2.Presentable.Basic
-- 本ファイルは drafts/Sheaves/{SheafCondition,GlobalSections}.lean を import する（要確認：F2 の空間の ∞ 圏と `SigmaPresheafInfinity` の名前）。

/-!
# 空間値の層と E 値の層の局所性（S8）

## 概要
site 𝒞 上の空間値前層 PSh(𝒞) = Fun(𝒞^op, 𝒮) とその J 層（Čech、HTT 6.2.2.6）、層化 L（HTT 6.2.2.7）、0 切り捨て（離散な前層の L は離散で
1 圏の層化に一致）、単射に沿う離散対象の押し出しの離散性、E 値の層 O の切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）、
O が J 層なら Γ(−, O) はすべての J 局所同値を同値に送ること（HTT 5.1.5.6 の極限保存延長 O^ と 5.5.4.20 の筋）、Γ(h_c, O) = O(c)。

## 方針
S4（E 値の層化）は `IsStable E` を仮定しているので、空間 𝒮 には HTT 6.2.2.7 の構成を別に置く。0 切り捨ては HTT 5.5.6.28（左完全な左随伴は
n 切り捨てを保つ）。局所性は O^ の逆像の類が強飽和で生成 sieve を含むこと。

## 規約
前層は S1 の `Presheaf 𝒞 E`（E = 𝒮）。1 圏の層は Mathlib の `Sheaf`（集合値）で、離散な前層との対応は nerve 経由（要確認）。

## 使われ方
Cor 8.12（A6-4）。A8（Thm 10.11）でも使う見込み。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 概要：S8-1：空間値前層の J 層化 L（HTT 6.2.2.7）。
方針：∞ トポスの左完全局所化。
規約：S4 と同じ `IsReflectiveSubcategory` の形で、E = 𝒮。
使われ方：以下。 -/
theorem sheafification_exists_spaces : True := by sorry -- HTT 6.2.2.7

/-- 概要：S8-2：離散（0 切り捨て）な前層の L は離散で、1 圏の層化（Mathlib `presheafToSheaf`）に一致。
方針：HTT 5.5.6.28、τ_{≤0} Sh(𝒞) ≃ Sh_{Set}(𝒞)。
規約：—
使われ方：局所同値の判定。 -/
theorem sheafify_discrete_eq : True := by sorry

/-- 概要：S8-2′：離散な前層の射 P → Q が 1 圏の層化で同型なら J 局所同値（L で同値）。 -/
theorem localEquiv_of_sheafifyIso : True := by trivial

/-- 概要：S8-3：単射に沿う離散な前層の押し出しは離散（点ごとに空間の押し出し、単射なら集合の押し出し）。 -/
theorem discretePushout_isDiscrete : True := by trivial

/-- 概要：S8-4：E 値の前層 O と空間値前層 F の切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。F ↦ Γ(F, O) は前層の余極限を極限に送る。
O の極限保存延長 O^ : PSh(𝒞)^op → E（HTT 5.1.5.6）と Γ(F, O) = O^(F)。
方針：元の圏 el(F)（F の Grothendieck 構成）上の極限。
規約：E 表示可能。
使われ方：Cor 8.12 の引き戻し。 -/
def sectionsOf : True := trivial
theorem sectionsOf_colimit : True := by trivial
theorem sectionsOf_representable : True := by trivial

/-- 概要：S8-5：O が J 層（S1 の `IsSheaf`）なら Γ(−, O) はすべての J 局所同値を同値に送る。
方針：O^ の逆像の類は強飽和（O^ は極限を保つ）で、生成 sieve h_S ↪ h_c を含む（層条件）ので J 局所同値を含む（HTT 5.5.4.20 の筋）。
規約：—
使われ方：Cor 8.12。 -/
theorem sections_localEquiv_iso : True := by sorry

/-- 概要：S8-6：F の元の圏が 1 圏 D のとき Γ(F, O) = lim_D O。特に F_T = Hom(T, −) で D = Perfd_{T/}。 -/
theorem sectionsOf_eq_limit_elements : True := by trivial

end SerrePositivity.InfinityCategories.Sheaves
