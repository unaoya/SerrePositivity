-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.Sheafification（S4、M12a、BS）。
-- 設計書：formalization-plans/bhatt-scholze/infinity-sheaves-design.md §8 の S4、foundation-entry-points.md §1.9・§4。型検査対象（5∞-0）。
-- 11-05 新設：S4 の生成辺は切断 Γ(X, F)（Sheaves/SetSections の `sectionsOf`）を使うので、GlobalSections から
-- `exists_sheafGeneratingEdges`・`sheafification_exists` を、SpaceValued から `sheafification_exists_spaces` をここへ移した。
module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Space
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
-- 本ファイルは drafts/Sheaves/{SheafCondition,SetSections,GlobalSections}.lean を import する。

/-!
# 層化の存在（S4、HTT 5.5.4.15・6.2.2.7）：被覆篩の生成辺

## 概要
presentable な E と小さい site (𝒞, J) について、E 値前層の層は、小さい辺族 W の局所対象としてちょうど特徴づけられる。
W は、被覆篩 S ∈ J U の包含 S ↪ h_U を離散な空間値前層の辺とみなし、E の検出族 M_i と空間とのテンソル（G8）で
送った辺 S ⊗ M_i → h_U ⊗ M_i の全体。これと `sheafification_of_generatingEdges`（G4・G6、GlobalSections）から層化が存在する。

## 方針
1. 篩の元の圏 `(sieveCategory S)ᵒᵖ` は篩の前層 `S.functor` の元の圏と同値で、射影は `sieveDiagram S` に一致する（1 圏）。
   よって Γ(S.functor, F) は F の S 上の制限図式の極限（指定錐を逆同値の nerve で制限する）。
2. Γ(h_U, F) ≃ F(U)（`sectionsOf_representable`）。包含 S ↪ h_U が誘導する Γ(h_U, F) → Γ(S, F) は、この二つの同一視の下で
   `restrictionCone F S` の比較射。よって「S で降下する ⇔ `sectionsOf_map S.functorInclusion` が可逆」。
3. G8 の自然な別版（IF-G2）：Map(X ⋙ ⊗M, F) ≃ Map(M, Γ(X, F)) の篩包含 S ↪ h_U に関する自然性だけを使うと、
   「辺 S ⊗ M → h_U ⊗ M について局所 ⇔ Map(M, −) が Γ(h_U, F) → Γ(S, F) を同値に送る」。
4. M が検出族なら、すべての i で同値 ⇔ Γ(h_U, F) → Γ(S, F) が可逆。1〜3 と合わせて「W 局所 ⇔ 層」。

## 規約
E は presentable（`hE`）。安定性は使わない（空間値・CAlg 値にも同じ補題を当てる）。検出族の存在は presentable 性から（要確認：F2 の名前）。

## 使われ方
本ファイルの `sheafification_exists`（D(A) 値）と `sheafification_exists_spaces`（S8-1）、
CAlgValued の `sheafification_exists_cAlg`（G12 の後）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.InfinityCategories.Sheaves

open CategoryTheory Limits SSet MonoidalCategory MonoidalClosed
open scoped Simplicial
open _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories (IsPresentable)

variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-! ## 1. 篩の元の圏（1 圏） -/

/-- 概要：篩 S の圏の反対は、篩の前層 `S.functor` の元の圏と同値。
方針：(f : V → U, f ∈ S) ↦ ⟨op V, f⟩。元の圏の射 ⟨op V, f⟩ → ⟨op V', f'⟩ は h : V' → V で h ≫ f = f'、すなわち篩の圏の f' → f。
規約：`sectionsOf_eq_limit_elements` の `e : D ≌ F.Elements` の形（D = (sieveCategory S)ᵒᵖ）。
使われ方：Γ(S.functor, F) を制限図式の極限に。 -/
def sieveElementsEquiv {U : 𝒞} (S : Sieve U) : (sieveCategory S)ᵒᵖ ≌ S.functor.Elements :=
  (sieveElementsEquivalence S).symm

/-- 概要：同値の後に元の圏の射影を取ると、篩の制限図式の形状 `sieveDiagram S` に一致する。
方針：対象 (f : V → U) ↦ op V、射 g ↦ g.op の両辺を比べる。
規約：関手の等号（`sectionsOf_eq_limit_elements` の図式をそのまま `restriction F S` に書き換えるため）。
使われ方：`sectionsOf_sieve`。 -/
theorem sieveElementsEquiv_functor_π {U : 𝒞} (S : Sieve U) :
    (sieveElementsEquiv S).functor ⋙ Functor.Elements.π S.functor = sieveDiagram S :=
  sieveCategoryToElements_comp_π S

/-! ## 2. 篩の切断と restrictionCone -/

/-- 概要：Γ(S.functor, F) は F の S 上の制限図式の極限：任意の極限錐の頂点と頂点同型。
方針：選んだ極限錐を `sieveElementsEquiv S` で制限し、図式を `restriction F S` に書き換え、指定錐 c と比較する。
規約：錐は呼び出し側が指定する。
使われ方：`isLimit_restrictionCone_iff_sectionsMap`。 -/
def sectionsOf_sieve (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram S.functor F))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (restriction F S)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (sectionsOf S.functor F h) c.vertex := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S))
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence j :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence (sieveElementsEquiv S)).isQCatEquivalence.ulift
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (sectionsOfCone S.functor F h) j
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape j hj _).mp
      (sectionsOfCone_isLimit S.functor F h)
  let d' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (restriction F S) :=
    ⟨d.val, d.property.trans (sieveSectionsDiagram_reindex S F)⟩
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d' := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq d d' rfl).mp hd
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso d' c hd' hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex c.vertex at e
  simpa only [d, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone_vertex, sectionsOf] using e

/-- 概要：包含 S ↪ h_U が誘導する Γ(h_U, F) → Γ(S, F) が可逆 ⇔ `restrictionCone F S` が極限錐（S で降下する）。
方針：Γ(h_U, F) ≃ F(U)（`sectionsOf_representable`）、Γ(S, F) ≃ lim（`sectionsOf_sieve`）。この二つの下で `sectionsOf_map` は
`restrictionCone F S` の頂点から極限への比較射に対応する（錐の脚がどちらも F(f) なので）。比較射が可逆 ⇔ 錐が極限錐。
規約：`HasLimit` は E の presentable 性から（`sectionsOfDiagram_hasLimit`）。
使われ方：`isSheaf_iff_sectionsMap`、S4 の局所性。 -/
theorem isLimit_restrictionCone_iff_sectionsMap (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U)
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram S.functor F))
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram (yoneda.obj U) F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F S) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (sectionsOf_map S.functorInclusion F hS hU) := by
  exact (sieveSectionsMap_isInvertible_iff S F
    (sectionsOfCone S.functor F hS) (sectionsOfCone_isLimit _ _ _)
    (sectionsOfCone (yoneda.obj U) F hU) (sectionsOfCone_isLimit _ _ _)).symm

/-- 概要：層 ⇔ すべての被覆篩の包含で切断の写像が可逆。
方針：`IsSheaf` の定義と `isLimit_restrictionCone_iff_sectionsMap`。
規約：`hE` で極限の存在を供給する。
使われ方：S4 の「W 局所 ⇔ 層」の右辺。 -/
theorem isSheaf_iff_sectionsMap (J : GrothendieckTopology 𝒞) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (F : Presheaf 𝒞 E) :
    IsSheaf J F ↔ ∀ (U : 𝒞) (S : Sieve U), S ∈ J U →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (sectionsOf_map S.functorInclusion F
        (sectionsOfDiagram_hasLimit hE S.functor F) (sectionsOfDiagram_hasLimit hE (yoneda.obj U) F)) := by
  exact isSheaf_iff_sieveSectionsMap_isInvertible J hE F

/-! ## 3. 検出族と生成辺 -/

/-- 概要：E の頂点の小さい族 M が辺の可逆性を検出する：e が可逆 ⇔ すべての i で Map(M_i, −) が e を同値に送る。
方針：presentable な E は κ-compact な対象の小さい集合で生成され、写像空間で同値を検出する（HTT 5.5.1.1・5.4.2）。
規約：射はホモトピー圏の射、写像空間は pinched Hom、後合成は `PinchedInterval.postcompose`（`IsLocalForHom` の
`PinchedInterval.precompose` の双対。HomotopyLimits/Presentable/LocalObjects と同じ書き方）。族の添字は `Type u`（E は `SSet.{u+1}`）。
使われ方：`isLocalObject_sheafGeneratingEdges_iff`。 -/
def IsDetectingFamily {ι : Type u} (M : ι → E _⦋0⦌) : Prop :=
  ∀ {x y : E _⦋0⦌} (f : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y),
    IsIso f ↔ ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose (M i) f)

/-- 概要：presentable な E は小さい検出族をもつ。
方針：`IsPresentable.exists_limitDetectingPresheafModel`（F2/Presentable/ReflectiveModelLimitDetection：小さい A と
R : C ⟶ PresheafInfinity A があり、錐が極限 ⇔ 各 a での評価で極限）を一点の図式に当てて「辺が同値 ⇔ 各評価で同値」、
評価を Map(g_a, −) と同一視する（IF-G2 の G14）。
要確認（IF-G2 G14：供給予定）。 -/
theorem exists_detectingFamily (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (ι : Type u) (M : ι → E _⦋0⦌), IsDetectingFamily M := by
  sorry -- IF-G2 G14

/-- 概要：被覆篩の包含 S ↪ h_U を離散な空間値前層の辺とみなし、G8 の空間とのテンソル ⊗M_i で E 値前層の辺 S ⊗ M_i → h_U ⊗ M_i に送る。
方針：G2 の `SetWeight.sieveTensorEdge` をそのまま使い、自然性の四角形と同じ指定辺を選ぶ。
規約：添字は (U, 被覆篩 S, i)。全体で Type u（𝒞 が小さいので）。
使われ方：S4 の辺族 W。 -/
def sheafGeneratingEdges (J : GrothendieckTopology 𝒞) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) {ι : Type u} (M : ι → E _⦋0⦌) :
    (Σ U : 𝒞, {S : Sieve U // S ∈ J U} × ι) → (PresheafCat 𝒞 E) _⦋1⦌ :=
  fun ⟨U, S, i⟩ => (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveTensorEdge S.val hE (M i)).edge

/-- 概要：W 局所 ⇔ 層。
方針：辺 S ⊗ M_i → h_U ⊗ M_i についての局所性は、G8 の自然な別版（IF-G2）を包含 S ↪ h_U に当てて、
Map(M_i, −) が Γ(h_U, F) → Γ(S, F)（`sectionsOf_map S.functorInclusion`）を同値に送ることと同値。M が検出族なので
すべての i で同値 ⇔ その辺が可逆。`isSheaf_iff_sectionsMap` で層条件に戻す。
規約：G8 の同値と自然性は IF-G2 の別版の名前で使う（G1 の `tensorSpaceFunctor_setWeightHom` は自然性が言えないので使わない）。
使われ方：`exists_sheafGeneratingEdges`。 -/
theorem isLocalObject_sheafGeneratingEdges_iff (J : GrothendieckTopology 𝒞) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {ι : Type u} (M : ι → E _⦋0⦌) (hM : IsDetectingFamily M) (F : (PresheafCat 𝒞 E) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range (sheafGeneratingEdges J hE M)) F ↔
      sheafProperty J F := by
  sorry -- 要確認（IF-G2：G8 の自然な別版 `tensorSpaceFunctor_setWeightHomNatural` とその自然性、篩の包含への特殊化）

/-! ## 4. 層化の存在（GlobalSections・SpaceValued から移した） -/

/-- 被覆篩の生成辺で層を特徴づける辺族がある。 -/
theorem exists_sheafGeneratingEdges (J : GrothendieckTopology 𝒞) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (I : Type u) (edges : I → (PresheafCat 𝒞 E) _⦋1⦌),
      ∀ F, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range edges) F ↔ sheafProperty J F := by
  obtain ⟨ι, M, hM⟩ := exists_detectingFamily hE
  exact ⟨_, sheafGeneratingEdges J hE M, isLocalObject_sheafGeneratingEdges_iff J hE M hM⟩

/-- S4（HTT 5.5.4.15）。presentable な係数について、被覆篩の生成辺から層化を得る。
`[IsStable E]` は従来の引数を保つために残す（証明では使わない）。 -/
theorem sheafification_exists (J : GrothendieckTopology 𝒞) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable E] (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    Sheafification J E := by
  obtain ⟨I, edges, hW⟩ := exists_sheafGeneratingEdges J hE
  exact sheafification_of_generatingEdges J hE edges hW

/-- 概要：S8-1：空間値前層の J 層化 L（HTT 6.2.2.7）。h𝒮 は `F2.Presentable.space_isPresentable` で与えられる。 -/
theorem sheafification_exists_spaces (J : GrothendieckTopology 𝒞) (h𝒮 : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    Sheafification J _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  obtain ⟨I, edges, hW⟩ := exists_sheafGeneratingEdges J h𝒮
  exact sheafification_of_generatingEdges J h𝒮 edges hW

end SerrePositivity.InfinityCategories.Sheaves
