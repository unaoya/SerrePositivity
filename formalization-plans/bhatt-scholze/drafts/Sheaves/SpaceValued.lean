-- 将来の置き場所（調整役の決定、main 7b8b96286、M12e）：S8-1・5・6 は SerrePositivity.InfinityCategories.Sheaves.SpaceValued.*、S8-2・3 は Sheaves.Discrete.*、
-- S8-4 の一般部分（HTT 5.1.5.6 の極限保存延長、el(F) 上の極限）は F2/（M12b と同じ）。前提：G13（𝒮 の presentable 性）、S4 の非安定版。時期・担当は M12 と同じ。
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.4、S8。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.F2.Presentable
-- 11-03：`F2.Presentable.Basic` は存在しない名前だった（DG-W3 の改名ではなく当初の推測）。F2 の束ねモジュール `F2.Presentable` に直した。
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

/-! ## 離散（集合値）の場合の入口（11-03、BS-D3 の D3-07。A6 はこの部分だけを使う） -/

variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u + 1}} [Quasicategory E]

/-- 概要：S8-2′ の 1 圏版：集合値前層の射 φ : P ⟶ Q が **J 局所同値**であること。定義は Mathlib の層化 `presheafToSheaf J (Type u)` で φ が同型になること。
方針：離散な前層では ∞ 層化 L と 1 圏の層化が一致する（S8-2、`sheafify_discrete_eq`）ので、これが HTT の J 局所同値の離散版。
規約：P・Q は `𝒞ᵒᵖ ⥤ Type u`（Mathlib の前層）。
使われ方：A6 `homPresheafPushout_localEquiv`、`sections_localEquiv_iso`。 -/
def IsLocalEquivSet (J : GrothendieckTopology 𝒞) {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) : Prop :=
  CategoryTheory.IsIso ((CategoryTheory.presheafToSheaf J (Type u)).map φ)

/-- 概要：S8-2′：離散な前層の射が 1 圏の層化で同型なら、空間値前層の射としても J 局所同値（L で同値）。∞ 側との橋（基盤待ち）。
方針：S8-2（`sheafify_discrete_eq`）。
規約：主張の形は空間値前層と L の名前が決まってから。
使われ方：`sections_localEquiv_iso` を ∞ の一般論から導く所。 -/
theorem localEquiv_of_sheafifyIso : True := by trivial -- 基盤待ち（S8-2 の後）

/-- 概要：単射に沿う集合値前層の押し出し（点ごとの集合の押し出し）。Mathlib の `pushout` をそのまま使う（離散なので S8-3 は自動）。
方針：`CategoryTheory.Limits.pushout` in `𝒞ᵒᵖ ⥤ Type u`。
規約：—
使われ方：A6 `homSheaf_pushout`。 -/
abbrev presheafPushout {P Q R : 𝒞ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) : 𝒞ᵒᵖ ⥤ Type u := CategoryTheory.Limits.pushout f g

/-- 概要：S8-3：単射に沿う離散な前層の押し出しは離散（点ごとに空間の押し出し、単射なら集合の押し出し）。 -/
theorem discretePushout_isDiscrete : True := by trivial

/-- 概要：S8-4：E 値の前層 O と空間値前層 F の切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。F ↦ Γ(F, O) は前層の余極限を極限に送る。
O の極限保存延長 O^ : PSh(𝒞)^op → E（HTT 5.1.5.6）と Γ(F, O) = O^(F)。
方針：元の圏 el(F)（F の Grothendieck 構成）上の極限。
規約：E 表示可能。
使われ方：Cor 8.12 の引き戻し。 -/
/-- 概要：Γ(F, O) の図式：F の元の圏 `F.Elements`（Mathlib `CategoryTheory.Functor.Elements`、射影 `CategoryOfElements.π F : F.Elements ⥤ 𝒞ᵒᵖ`）の nerve を
持ち上げて O と合成したもの。
方針：S3 の `cechShape` と同じ持ち上げ。
規約：F は集合値（`𝒞ᵒᵖ ⥤ Type u`）、O は S1 の `Presheaf 𝒞 E`（= `presheafShape 𝒞 ⟶ E`、`presheafShape 𝒞` は nerve 𝒞ᵒᵖ の持ち上げ）。
使われ方：`sectionsOf`。 -/
def sectionsOfDiagram (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve F.Elements) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.CategoryOfElements.π F)) ≫ O

/-- 概要：E が表示可能なら上の図式は極限をもつ（添字は小さい）。 -/
theorem sectionsOfDiagram_hasLimit (hE : F2.Presentable.IsPresentable E) (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
    HasLimit (sectionsOfDiagram F O) := by sorry -- 基盤待ち（G13 の系）

/-- 概要：S8-4：切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。選んだ極限錐の頂点。
方針：S2 の `globalSections` と同じ選び方。
規約：E 表示可能（`HasLimit` を引数で受ける）。
使われ方：Cor 8.12 の引き戻し。 -/
def sectionsOfCone (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) : JoinCone (sectionsOfDiagram F O) :=
  sorry -- 選んだ極限錐
def sectionsOf (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) : E _⦋0⦌ :=
  (sectionsOfCone F O h).vertex
theorem sectionsOfCone_isLimit (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) :
    IsLimitCone (sectionsOfCone F O h) := by sorry

/-- 概要：Γ(−, O) の関手性：φ : P ⟶ Q に対し Γ(Q, O) → Γ(P, O)（元の圏の関手 P.Elements ⥤ Q.Elements に沿う制限と極限の普遍性）。
方針：錐の制限。
規約：E の辺。
使われ方：`sections_localEquiv_iso`、押し出しの比較。 -/
def sectionsOf_map {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf 𝒞 E)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
    SSet.Edge (sectionsOf Q O hQ) (sectionsOf P O hP) := sorry

/-- 概要：S8-4 の余極限との両立：Γ(−, O) は集合値前層の押し出しを E の引き戻しに送る（極限保存延長 O^ は余極限を極限に）。A6 で要るのは押し出し一つ。
方針：el(pushout) 上の極限を三つの元の圏の極限の引き戻しに分解（HTT 5.1.5.6 の O^ が余極限を保つこと）。
規約：主張の形（E の引き戻し四角形の述語）は基盤の名前が決まってから。
使われ方：Cor 8.12（F_{S′} ⊔_{F_{S′/I}} F_{S/I} の切断）。 -/
theorem sectionsOf_pushout : True := by trivial -- 基盤待ち（引き戻し四角形の述語）
theorem sectionsOf_colimit : True := by trivial -- 一般の余極限（記録）

/-- 概要：Γ(h_c, O) ≃ O(c)（表現可能な前層の元の圏は終対象 (c, id) をもつ）。
方針：終対象上の極限。
規約：`VertexIso`。
使われ方：Γ(F_T, O) の計算の端。 -/
def sectionsOf_representable (c : 𝒞) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram (CategoryTheory.yoneda.obj c) O)) :
    VertexIso (sectionsOf (CategoryTheory.yoneda.obj c) O h) (O.app _ (ULift.up (nerveVertex (Opposite.op c)))) := sorry

/-- 概要：S8-5：O が J 層（S1 の `IsSheaf`）なら Γ(−, O) はすべての J 局所同値を同値に送る。
方針：O^ の逆像の類は強飽和（O^ は極限を保つ）で、生成 sieve h_S ↪ h_c を含む（層条件）ので J 局所同値を含む（HTT 5.5.4.20 の筋）。
規約：—
使われ方：Cor 8.12。 -/
theorem sections_localEquiv_iso (J : GrothendieckTopology 𝒞) {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
    (O : Presheaf 𝒞 E) (hO : IsSheaf J O)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
    IsInvertibleEdge (sectionsOf_map φ O hP hQ) := by
  sorry -- 基盤待ち：O^ の逆像の類は強飽和で生成 sieve を含む（HTT 5.5.4.20 の筋）。要確認：`IsInvertibleEdge` の名前空間

/-- 概要：S8-6：F の元の圏と同値な 1 圏 D（e : D ≌ F.Elements）があれば Γ(F, O) は D 上の極限（e に沿う制限は極限錐を保つ）。特に F_T = Hom(T, −) で D = Perfd_{T/}。
方針：同値に沿う制限と極限の不変性。
規約：`VertexIso`。
使われ方：A6 `sectionsOf_homSheaf_eq_perfectoidization`（A5 の `perfectoidization_isLimit` の錐と結ぶ）。 -/
def sectionsOf_eq_limit_elements (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O))
    {D : Type u} [SmallCategory D] (e : D ≌ F.Elements)
    (c : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (e.functor ⋙ CategoryTheory.CategoryOfElements.π F)) ≫ O))
    (hc : IsLimitCone c) : VertexIso (sectionsOf F O h) c.vertex := sorry

end SerrePositivity.InfinityCategories.Sheaves
