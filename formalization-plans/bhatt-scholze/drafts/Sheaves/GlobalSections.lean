-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.GlobalSections（層 Sheaves）
-- 設計書：formalization-plans/bhatt-scholze/infinity-sheaves-design.md §1・§3、単位 S2（層化は S4 の入力として仮定）。
-- 基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
-- 本ファイルは drafts/Sheaves/SheafCondition.lean（将来 …Sheaves.SheafCondition）を import する。

/-!
# 大域切断と RΓ（∞ topos の Γ(F) = Map(1, F) = lim F）

## 概要
E 値前層 F の大域切断 Γ(F) を F の添字全体（N(𝒞)^op）上の極限として、層化 F ↦ F^♯ を層のなす充満部分 ∞ 圏への反射として、
RΓ(J, F) := Γ(F^♯) を定める。層化の存在（HTT 5.5.4.15、E が安定・presentable のとき）は S4 の定理で、ここでは反射のデータを
入力にとる。

## 方針
Γ は `Core.HasLimit`・`IsLimitCone` で述べ、極限錐を選んで頂点を取る。E が presentable なら小さい形状の極限が存在する
（`IsPresentable.hasLimit`）。層化は F2/Presentable の `IsReflectiveSubcategory` を、関手 ∞ 圏 `(ihom (presheafShape 𝒞)).obj E` の
頂点のうち層であるものに適用する。

## 規約
RΓ は Čech 層の層化で定義する。古典的な層係数コホモロジー（＝hypersheaf 化の Γ）とは、非有界な前層で異なりうる。
離散（有界）な Čech 層では一致する（`isSheaf_discrete_hypercomplete` の形で A0 に置く。設計書 §2.1、ノート第 4 章 D17）。
`derivedGlobalSections` の値は選んだ極限錐の頂点で、使う側は頂点の等号でなく `IsLimitCone` の普遍性で扱う（E3 の `BSLimitConeData` と同じ）。

## 使われ方
A0 Not 4.16（Δ_{R/A} = RΓ((R/A)_Δ, O_Δ)）、A5 Prop 8.5、A6 Cor 8.11。Frobenius など前層の射に沿う関手性は `derivedGlobalSections_map`。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Sheaves

open _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories (IsPresentable)

variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u + 1}} [Quasicategory E]

/-! ## 大域切断 -/

/-- 概要：前層 F の大域切断の錐：添字全体の上の極限錐。
方針：`HasLimit F` から錐を選ぶ。
規約：選択を含む。頂点の等号は主張しない。
使われ方：`globalSections`。 -/
def globalSectionsCone (F : Presheaf 𝒞 E) (h : HasLimit F) : JoinCone F :=
  h.choose

lemma globalSectionsCone_isLimit (F : Presheaf 𝒞 E) (h : HasLimit F) :
    IsLimitCone (globalSectionsCone F h) :=
  h.choose_spec

/-- 概要：大域切断 Γ(F) = lim_{N(𝒞)^op} F。
方針：選んだ極限錐の頂点。
規約：E の頂点。
使われ方：RΓ の定義。Mathlib の 1 圏版は `Sheaf.ΓNatIsoLim`。 -/
def globalSections (F : Presheaf 𝒞 E) (h : HasLimit F) : E _⦋0⦌ :=
  (globalSectionsCone F h).vertex

/-- 概要：E が presentable なら任意の前層が大域切断を持つ。
方針：`IsPresentable.hasLimit`（形状 `nerve 𝒞ᵒᵖ : SSet.{u}` を持ち上げたもの）。
規約：𝒞 が小さいことを使う。
使われ方：Γ の存在。 -/
lemma hasLimit_presheaf (hE : IsPresentable E) (F : Presheaf 𝒞 E) : HasLimit F :=
  hE.hasLimit F

/-! ## 層化（反射のデータ） -/

/-- 概要：前層の関手 ∞ 圏（HTT 1.2.7.3）。
方針：内部 Hom `ihom`。頂点が `Presheaf 𝒞 E` に対応する。
規約：quasicategory（E が quasicategory なら ihom もそう）。
使われ方：層化を反射的部分圏として述べる土台。 -/
abbrev PresheafCat (𝒞 : Type u) [SmallCategory 𝒞] (E : SSet.{u + 1}) : SSet.{u + 1} :=
  (ihom (presheafShape 𝒞)).obj E

/-- 概要：関手 ∞ 圏の頂点を単体的集合の射として読む。
方針：`functorVertex` の逆（Core/FullSubcomplexInternalHom）。
規約：全単射。
使われ方：`sheafProperty`。
Core の `functorVertexEquiv` を使う。 -/
def vertexToPresheaf (F : (PresheafCat 𝒞 E) _⦋0⦌) : Presheaf 𝒞 E :=
  (functorVertexEquiv _ _).symm F

/-- 概要：関手 ∞ 圏の頂点が J 層であるという性質。
方針：`IsSheaf` を `vertexToPresheaf` で引き戻す。
規約：Prop。
使われ方：層の充満部分 ∞ 圏、反射。 -/
def sheafProperty (J : GrothendieckTopology 𝒞) : (PresheafCat 𝒞 E) _⦋0⦌ → Prop :=
  fun F => IsSheaf J (vertexToPresheaf F)

/-- 概要：層化のデータ：層への反射。
方針：F2/Presentable の `IsReflectiveSubcategory`（左随伴付きの充満部分圏）。
規約：存在は S4（`sheafification_exists`）。ここでは与えられたものとして使う。
使われ方：RΓ。 -/
abbrev Sheafification (J : GrothendieckTopology 𝒞) (E : SSet.{u + 1}) [Quasicategory E] : Prop :=
  IsReflectiveSubcategory (PresheafCat 𝒞 E) (sheafProperty (E := E) J)

/-- 小さい辺族の局所対象がちょうど層なら、前層圏の Bousfield 反射が層化を与える。 -/
theorem sheafification_of_generatingEdges (J : GrothendieckTopology 𝒞) (hE : IsPresentable E)
    {I : Type u} (edges : I → (PresheafCat 𝒞 E) _⦋1⦌)
    (hW : ∀ F, HomotopyLimits.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range edges) F ↔ sheafProperty J F) :
    Sheafification J E := by
  have hP : IsPresentable (PresheafCat 𝒞 E) :=
    F2.Presentable.functor_isPresentable (nerve 𝒞ᵒᵖ) hE
  have h : HomotopyLimits.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range edges) =
      sheafProperty (E := E) J :=
    funext fun F => propext (hW F)
  unfold Sheafification
  rw [← h]
  exact F2.Presentable.Localization.bousfield_isReflectiveSubcategory hP edges

-- `exists_sheafGeneratingEdges`・`sheafification_exists`（S4）は drafts/Sheaves/SheafGenerators.lean へ移した（11-05。切断 Γ の比較は SetSections に分離）。

/-- 同じ反射の選択を層化の頂点、射、単位に使う。 -/
def sheafificationFunctor (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E) :
    PresheafCat 𝒞 E ⟶ PresheafCat 𝒞 E :=
  (Classical.choice hJ).localization

/-- 概要：与えられた反射で F を層化した前層 F^♯。
方針：反射関手の頂点での値を `vertexToPresheaf` で読む。
規約：選択を含む（反射関手の選択）。
使われ方：RΓ。
選んだ反射の自己関手を評価する。 -/
def sheafify (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E) (F : Presheaf 𝒞 E) :
    Presheaf 𝒞 E :=
  vertexToPresheaf ((sheafificationFunctor J hJ).app _ (functorVertex F))

lemma isSheaf_sheafify (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E) (F : Presheaf 𝒞 E) :
    IsSheaf J (sheafify J hJ F) := by
  sorry -- 反射の像は部分圏に入る

/-- 概要：層化の単位 F → F^♯（前層の射＝単体的ホモトピー）。
方針：随伴の単位の成分。
規約：E3 の `NatInfinity`（`SSet.Homotopy`）と同じ形。
使われ方：層の場合に F^♯ ≃ F（`sheafify_of_isSheaf`）、RΓ の関手性。 -/
def sheafifyUnit (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E) (F : Presheaf 𝒞 E) :
    SSet.Homotopy F (sheafify J hJ F) :=
  by
    apply functorHomHomotopy
    have hv : functorVertex (sheafify J hJ F) = (sheafificationFunctor J hJ).app _ (functorVertex F) :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change HomotopyCategory.mk (functorVertex F) ⟶ HomotopyCategory.mk (functorVertex (sheafify J hJ F))
    rw [hv]
    exact functorHomEvaluate (Classical.choice hJ).unit (functorVertex F)

/-- 概要：層の層化は（単位を通して）自分自身。
方針：反射的部分圏の対象で単位は同値。
規約：同値は関手 ∞ 圏の辺の可逆性で述べる。
使われ方：Cor 3.12 の後、RΓ(O_Δ) = Γ(O_Δ)。 -/
lemma sheafifyUnit_isEquivalence_of_isSheaf (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E)
    {F : Presheaf 𝒞 E} (hF : IsSheaf J F) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (sheafifyUnit J hJ F)) := by
  sorry -- 反射の単位は層で可逆。h Fun の単位を表すこの辺も可逆

/-! ## RΓ -/

/-- 概要：RΓ(J, F) := Γ(F^♯)。
方針：層化してから大域切断。
規約：値は選んだ極限錐の頂点。Čech 層の RΓ（モジュールの規約）。
使われ方：A0 Not 4.16、A5 Prop 8.5、A6 Cor 8.11。 -/
def derivedGlobalSections (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E)
    (hE : IsPresentable E) (F : Presheaf 𝒞 E) : E _⦋0⦌ :=
  globalSections (sheafify J hJ F) (hasLimit_presheaf hE _)

/-- 概要：RΓ の錐：F^♯ 上の極限錐。F 自身の上の錐は、F が層で単位 F → F^♯ が同値のときに移送して得る（一般の F では Γ(F^♯) → F は得られない、W9-I-07）。
方針：`globalSectionsCone`。
規約：使う側はこの錐の普遍性で RΓ を特徴づける（E3 の `BSLimitConeData` と同じ規約）。
使われ方：脚注 10 の補題との比較。 -/
def derivedGlobalSectionsCone (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E)
    (hE : IsPresentable E) (F : Presheaf 𝒞 E) : JoinCone (sheafify J hJ F) :=
  globalSectionsCone (sheafify J hJ F) (hasLimit_presheaf hE _)

/-- 概要：層 F については RΓ(J, F) は F 自身の極限（Γ(F)）。
方針：`sheafifyUnit_isEquivalence_of_isSheaf` と、同値な図式の極限の比較。
規約：同値は E の辺の可逆性。
使われ方：Cor 3.12 の後に Δ_{R/A} = lim O_Δ、脚注 10 で Tot と比較。 -/
theorem derivedGlobalSections_of_isSheaf (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E)
    (hE : IsPresentable E) {F : Presheaf 𝒞 E} (hF : IsSheaf J F) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F := by
  sorry -- 単位が同値なので F 上の極限錐へ移送

/-- 概要：前層の射 F → G（単体的ホモトピー）から RΓ の辺 RΓ(F) → RΓ(G)。
方針：層化の関手性と極限の関手性。
規約：辺は E の 1 単体。
使われ方：O_Δ の Frobenius から Δ_{R/A} の Frobenius（A0）。 -/
def derivedGlobalSections_map (J : GrothendieckTopology 𝒞) (hJ : Sheafification J E)
    (hE : IsPresentable E) {F G : Presheaf 𝒞 E} (η : SSet.Homotopy F G) :
    E.Edge (derivedGlobalSections J hJ hE F) (derivedGlobalSections J hJ hE G) :=
  sorry -- 層化の関手性と極限の普遍性

/-- 概要：位相を粗くしても層である前層の RΓ は変わらない（Rem 4.5 の形）。
方針：J ≤ J′ で F が J′ 層なら J 層でもあり、どちらの RΓ も Γ(F)。
規約：`derivedGlobalSections_of_isSheaf` の系。
使われ方：原典 Rem 4.5・Prop 8.5 の「位相によらない」。 -/
theorem derivedGlobalSections_of_le (J J' : GrothendieckTopology 𝒞) (h : J ≤ J')
    (hJ : Sheafification J E) (hJ' : Sheafification J' E) (hE : IsPresentable E)
    {F : Presheaf 𝒞 E} (hF : IsSheaf J' F) :
    ∃ e : E.Edge (derivedGlobalSections J hJ hE F) (derivedGlobalSections J' hJ' hE F), IsInvertibleEdge e.toTruncated := by
  sorry -- 両位相の RΓ は F 上の極限。比較する辺は E 内にある（W9-I-03）

end SerrePositivity.InfinityCategories.Sheaves
