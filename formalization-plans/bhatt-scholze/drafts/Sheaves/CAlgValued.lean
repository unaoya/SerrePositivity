-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.CAlgValued（層 Sheaves。ただし CAlg_R は EInfinity にあるので、EInfinity の上か Sheaves の E の実例として）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-11、a2-design.md §2.2・G-A2-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

-- 本ファイルは drafts/Sheaves/{SheafCondition,GlobalSections,SheafGenerators,CechConerveLimit}.lean を E := CAlg_R A で使う。

/-!
# E∞-A 代数に値をとる層と RΓ（Sheaves 層の E = CAlg_A の実例）

## 概要
Sheaves 層の層条件・層化・Γ・RΓ・脚注 10 の補題は値の圏 E を任意の quasicategory として書いてあるので、E := CAlg_A（EInfinity の `CAlg_R A`、
E∞-A 代数の ∞ 圏）でそのまま使える。ここでは、忘却 U : CAlg_A → D(A)（`cAlgForgetDerived`）が極限錐を保ち反映することから、
CAlg_A 値の層条件・RΓ が D(A) 値のそれと両立することを述べる。これにより Δ_{R/A} に E∞ 構造が載り（A2 の値の圏）、
Čech–Alexander 模型の E∞ 構造（Shared/CosimplicialEInfinity）と比較できる。

## 方針
U は極限錐を保つ（`cAlgForgetDerived_mapJoinCone_isLimit_of_transport`、HA 3.2.2.5）。U は保存的（E∞ 代数の射で下の D(A) の射が同値なら同値）
ので、CAlg_A に極限が存在すれば U は極限錐を反映する。層条件は極限錐の条件なので、CAlg_A 値前層 F が層 ⇔ U ∘ F が層。
層化と RΓ は CAlg_A が presentable（G12）なら Sheaves 層の S2・S4 から。

## 規約
CAlg_A の presentable 性（G12）と小極限の存在は入力（EInfinity の到達点に依存）。U の同値反映は forget_conservative に分ける。

## 使われ方
A2-2（Δ の値の圏 𝒱 = (p,d) 完備な CAlg_A）、A4（Def 8.2 の E∞ 代数としての S_perfd）、E3 の CAlg 版（`PerfectoidizationInterfaceCAlg`）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.InfinityCategories.Sheaves

open _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories (IsPresentable)

variable {𝒞 : Type u} [SmallCategory 𝒞] (J : GrothendieckTopology 𝒞) (A : Type u) [CommRing A]

/-- 概要：CAlg_A 値前層の忘却像（D(A) 値前層）。
方針：`cAlgForgetDerived A` で後合成。
規約：—
使われ方：層条件の比較。 -/
def forgetPresheaf (F : Presheaf 𝒞 (E.CAlg A)) : Presheaf 𝒞 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  F ≫ E.forget A

/-- 概要：U は極限錐を保つ（HA 3.2.2.5。EInfinity の既存定理）。
方針：`cAlgForgetDerived_mapJoinCone_isLimit_of_transport`。
規約：FreeProbeDerivedFreeForget の系が transport の証人を供給する。
使われ方：層 ⇒ 忘却像が層。 -/
theorem forget_isLimitCone {K : SSet.{u + 1}} {D : K ⟶ E.CAlg A} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (E.forget A)) := E.forget_preservesLimits A c hc

/-- 概要：U は保存的：E∞ 代数の射で下の D(A) の射が可逆なら可逆。
方針：Barratt–Eccles 代数の弱同値は下の複体の擬同型（モデル圏の定義）。
規約：—
使われ方：極限錐の反映。
要確認：EInfinity に同じ主張があるか（`AlgebraRelativeComparisons` 付近）。 -/
theorem forget_conservative {x y : (E.CAlg A) _⦋0⦌} (e : SSet.Edge x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map (E.forget A)).toTruncated) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := E.forget_conservative A e he

/-- 概要：CAlg_A に極限が存在すれば、U は極限錐を反映する（保存的 ＋ 保存）。
方針：標準：極限錐との比較射が U で同値になり、保存性で同値。
規約：極限の存在は G12（presentable）から。
使われ方：CAlg_A 値の層条件 ⇔ D(A) 値の層条件。 -/
theorem forget_reflects_isLimitCone (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A)) {K : SSet.{u + 1}} {D : K ⟶ E.CAlg A}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (E.forget A))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  sorry

/-- 概要：CAlg_A 値前層が J 層 ⇔ その忘却像が J 層。
方針：層条件は極限錐の条件。U が極限錐を保ち反映。
規約：CAlg_A の presentable 性を仮定。
使われ方：Cor 3.12 を D(A) 値で示して CAlg_A 値へ移す。 -/
theorem isSheaf_iff_forget (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A)) (F : Presheaf 𝒞 (E.CAlg A)) :
    IsSheaf J F ↔ IsSheaf J (forgetPresheaf (E := E) A F) := by
  sorry

/-- 概要：CAlg_A 値の層化の存在（S4 を E = CAlg_A で）。
方針：`exists_sheafGeneratingEdges` に hA を渡し、`sheafification_of_generatingEdges` で層への反射を得る。
規約：G12 が hA を供給する。生成辺の構成は G8 待ち。
使われ方：RΓ_CAlg。
W9-I-05：U が極限を保つことから出るのは層条件の保存・反映まで。**層化と U の両立**（CAlg 値の単位の U 像が D(A) 値の局所同値であること）は別の一般補題
（S4 の非安定版、M12e の前提）で、ここでは主張だけ置く（`forget_sheafify`）。既に層である前層（O_Δ）については極限保存だけで比較が取れる。 -/
theorem sheafification_exists_cAlg (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A)) : Sheafification J (E.CAlg A) := by
  obtain ⟨I, edges, hW⟩ := exists_sheafGeneratingEdges J hA
  exact sheafification_of_generatingEdges J hA edges hW

/-- 概要：RΓ_CAlg(J, F) := Γ(F^♯)（CAlg_A 値）。
方針：S2 の `derivedGlobalSections` を E = CAlg_A で。
規約：—
使われ方：A2 の Δ_0。 -/
def derivedGlobalSectionsCAlg (hJ : Sheafification J (E.CAlg A)) (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A))
    (F : Presheaf 𝒞 (E.CAlg A)) : (E.CAlg A) _⦋0⦌ :=
  derivedGlobalSections J hJ hA F

/-- 概要：忘却は RΓ と両立：U(RΓ_CAlg(F)) ≃ RΓ_{D(A)}(U ∘ F)。
方針：U は極限錐を保ち、層化と両立（層の忘却像は層、単位の忘却像は D(A) 値の層化の単位に同値）。
規約：同値は D(A) の可逆な辺。
使われ方：A0 の D(A) 値の Δ と A2 の CAlg 値の Δ の一致。 -/
def forget_sheafify (hJ : Sheafification J (E.CAlg A)) (hJ' : Sheafification J (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (F : Presheaf 𝒞 (E.CAlg A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sheafify J hJ' (forgetPresheaf (E := E) A (sheafify J hJ F)))
      (sheafify J hJ' (forgetPresheaf (E := E) A F)) := by
  sorry -- S4：CAlg 値の単位の忘却は D(A) 値の局所同値。忘却した層は既に層

def forget_derivedGlobalSections (hJ : Sheafification J (E.CAlg A)) (hJ' : Sheafification J (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A)) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) (F : Presheaf 𝒞 (E.CAlg A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((E.forget A).app _ (derivedGlobalSectionsCAlg (E := E) J A hJ hA F))
      (derivedGlobalSections J hJ' hD (forgetPresheaf (E := E) A F)) := by
  sorry -- 忘却は極限を保つ。forget_sheafify と層の単位で二つの極限錐を比較

/-- 概要：環の前層（O_Δ のような離散な環の前層）を CAlg_A 値前層として読む（離散埋め込み CommRing_A → CAlg_A）。
方針：EInfinity の離散代数の埋め込み（`algebraEmbeddingForgetIso` の始域）。
規約：忘却像は `J A ∘ O`（D(A) の離散埋め込み）。
使われ方：A0 の O_Δ を CAlg 値に。 -/
def ringPresheafToCAlg (O : 𝒞ᵒᵖ ⥤ Under (CommRingCat.of A)) : Presheaf 𝒞 (E.CAlg A) := sorry
-- W9-I-06：入力は A 代数値の関手（`Under (CommRingCat.of A)`）。A0 の `structurePresheaf` は `toHom` で A 代数構造をもつのでこの形で与える。

end SerrePositivity.InfinityCategories.Sheaves
