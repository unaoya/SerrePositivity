-- 将来の置き場所（調整役の決定、main 7b8b96286、M12e）：S8-1・5・6 は SerrePositivity.InfinityCategories.Sheaves.SpaceValued.*、S8-2・3 は Sheaves.Discrete.*、
-- S8-4 の一般部分（HTT 5.1.5.6 の極限保存延長、el(F) 上の極限）は F2/（M12b と同じ）。前提：G13（離散空間と 0 切り捨て）、S4 の生成辺。時期・担当は M12 と同じ。
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.4、S8。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.InfinityCategories.Project.Entrypoints.Presentable
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Elements
-- 11-03：`F2.Presentable.Basic` は存在しない名前だった（DG-W3 の改名ではなく当初の推測）。F2 の束ねモジュール `F2.Presentable` に直した。
-- 本ファイルは drafts/Sheaves/{SheafCondition,SetSections,GlobalSections}.lean を import する。

/-!
# 空間値の層と E 値の層の局所性（S8）

## 概要
site 𝒞 上の空間値前層 PSh(𝒞) = Fun(𝒞^op, 𝒮) とその J 層（Čech、HTT 6.2.2.6）、層化 L（HTT 6.2.2.7）、0 切り捨て（離散な前層の L は離散で
1 圏の層化に一致）、単射に沿う離散対象の押し出しの離散性、E 値の層 O の切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）、
O が J 層なら Γ(−, O) はすべての J 局所同値を同値に送ること（HTT 5.1.5.6 の極限保存延長 O^ と 5.5.4.20 の筋）、Γ(h_c, O) = O(c)。

## 方針
空間 𝒮 の層化には S4 の生成辺と Bousfield 反射を適用する。0 切り捨ては HTT 5.5.6.28（左完全な左随伴は
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

open CategoryTheory Limits SSet MonoidalCategory MonoidalClosed
open scoped Simplicial
open _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories (IsPresentable)

-- SpaceInfinity・spaceInfinity_quasicategory は F1/Categories/CatInfinity、setsToKan・discreteSpaceInclusion・
-- Is0TruncatedSpace と前層の比較定理は F1/Categories/DiscreteSpace（IF-G1 G13、main 7bda72c3c）の実体。
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 集合値前層を点ごとに離散 Kan 複体へ送り、その図式の coherent nerve を取る。 -/
def discretePresheaf (P : 𝒞ᵒᵖ ⥤ Type u) : Presheaf 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan)

/-- 離散前層の U での値は P(U) の離散空間。 -/
theorem discretePresheaf_vertex (P : 𝒞ᵒᵖ ⥤ Type u) (U : 𝒞) :
    (discretePresheaf P).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (P.obj (Opposite.op U))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion_diagramVertex P (Opposite.op U)

/-- 集合値前層の自然変換を Kan 値図式の辺として実現する離散埋め込み。 -/
def kanDiscretePresheafInclusion (𝒞 : Type u) [SmallCategory 𝒞] :
    {I : nerve (𝒞ᵒᵖ ⥤ Type u) ⟶ PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} //
      (∀ P, I.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discretePresheaf P)) ∧
      (∀ {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q), ((nerve.edgeMk φ).map I).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge (F := ⟨P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan, trivial⟩) (G := ⟨Q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan, trivial⟩)
          (Functor.whiskerRight (Functor.whiskerRight φ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).edge)} := by
  sorry -- 射列を各対象で評価し、集合の全ての写像を setsToKan で送って curry

/-- Kan 値図式から作った同じ埋め込みの頂点と辺を点ごとに記述する。 -/
def discretePresheafInclusion (𝒞 : Type u) [SmallCategory 𝒞] :
    {I : nerve (𝒞ᵒᵖ ⥤ Type u) ⟶ PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} //
      (∀ P, I.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discretePresheaf P)) ∧
      (∀ {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (U : 𝒞),
        ((nerve.edgeMk φ).map (I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))))).edge =
          ((nerve.edgeMk (φ.app (Opposite.op U))).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion).edge)} := by
  let K := kanDiscretePresheafInclusion 𝒞
  refine ⟨K.val, K.property.1, ?_⟩
  intro P Q φ U
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion_presheafInclusion_edge K.val φ (K.property.2 φ) (Opposite.op U)

/-- φ の像の U 成分は、集合の写像 φ(U) を離散埋め込みで送った一単体。 -/
theorem discretePresheafInclusion_edge {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (U : 𝒞) :
    ((nerve.edgeMk φ).map ((discretePresheafInclusion 𝒞).val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))))).edge =
        ((nerve.edgeMk (φ.app (Opposite.op U))).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion).edge :=
  (discretePresheafInclusion 𝒞).property.2 φ U

/-- 上の離散埋め込みの本質像として 0 切り捨てを述べる。 -/
def Is0Truncated (x : (PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) _⦋0⦌) : Prop :=
  ∃ P : 𝒞ᵒᵖ ⥤ Type u, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discretePresheaf P)))

/-- 離散前層の本質像は点ごとの 0 切り捨てで判定できる。 -/
theorem is0Truncated_iff_pointwise (x : (PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) _⦋0⦌) :
    Is0Truncated x ↔ ∀ U : 𝒞,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))) := by
  sorry -- ⇒ は `discretePresheaf_vertex` と点ごとの評価、⇐ は各点の離散空間 `Is0TruncatedSpace` の証人から P を組み、
        -- 点ごとの頂点同型を関手 ∞ 圏の頂点同型へ（各点で可逆な辺は可逆、Core）

-- S8-1 `sheafification_exists_spaces` は drafts/Sheaves/SheafGenerators.lean へ移した（11-05）。

/-- 概要：S8-2：離散（0 切り捨て）な前層の L は離散で、1 圏の層化（Mathlib `presheafToSheaf`）に一致。
方針：HTT 5.5.6.28、τ_{≤0} Sh(𝒞) ≃ Sh_{Set}(𝒞)。
規約：—
使われ方：局所同値の判定。 -/
def sheafify_discrete_eq (J : GrothendieckTopology 𝒞) (hJ : Sheafification J _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (P : 𝒞ᵒᵖ ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sheafify J hJ (discretePresheaf P))
      (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj)) := by
  sorry -- 左完全な層化は 0 切り捨てを保ち、その反射は集合値の層化

/-! ## 離散（集合値）の場合の入口（11-03、BS-D3 の D3-07。A6 はこの部分だけを使う） -/


/-- 概要：S8-2′ の 1 圏版：集合値前層の射 φ : P ⟶ Q が **J 局所同値**であること。定義は Mathlib の層化 `presheafToSheaf J (Type u)` で φ が同型になること。
方針：離散な前層では ∞ 層化 L と 1 圏の層化が一致する（S8-2、`sheafify_discrete_eq`）ので、これが HTT の J 局所同値の離散版。
規約：P・Q は `𝒞ᵒᵖ ⥤ Type u`（Mathlib の前層）。
使われ方：A6 `homPresheafPushout_localEquiv`、`sections_localEquiv_iso`。 -/
def IsLocalEquivSet (J : GrothendieckTopology 𝒞) {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) : Prop :=
  CategoryTheory.IsIso ((CategoryTheory.presheafToSheaf J (Type u)).map φ)

/-- 概要：S8-2′：離散な前層の射が 1 圏の層化で同型なら、空間値前層の射としても J 局所同値（L で同値）。∞ 側との橋（基盤待ち）。
方針：S8-2（`sheafify_discrete_eq`）。
規約：同じ反射で前層の射を写した ihom の辺の可逆性。
使われ方：`sections_localEquiv_iso` を ∞ の一般論から導く所。 -/
theorem localEquiv_of_sheafifyIso (J : GrothendieckTopology 𝒞) (hJ : Sheafification J _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk φ).map ((discretePresheafInclusion 𝒞).val ≫ sheafificationFunctor J hJ)).toTruncated := by
  sorry -- sheafify_discrete_eq の自然性により、層化した φ の同型に対応する

/-- 概要：単射に沿う集合値前層の押し出し（点ごとの集合の押し出し）。Mathlib の `pushout` をそのまま使う（離散なので S8-3 は自動）。
方針：`CategoryTheory.Limits.pushout` in `𝒞ᵒᵖ ⥤ Type u`。
規約：—
使われ方：A6 `homSheaf_pushout`。 -/
abbrev presheafPushout {P Q R : 𝒞ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) : 𝒞ᵒᵖ ⥤ Type u := CategoryTheory.Limits.pushout f g

/-- 集合値の押し出しの可換四角形を二つの合成二単体ごと離散埋め込みで写す。 -/
def discretePushoutSquare {P Q R : 𝒞ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) :
    (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  let σ : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ nerve (𝒞ᵒᵖ ⥤ Type u) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout).desc
      (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ g (pushout.inr f g)))
      (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f (pushout.inl f g))) (by
        apply SSet.yonedaEquiv.injective
        change (nerve _).δ 1 (ComposableArrows.mk₂ g (pushout.inr f g)) =
          (nerve _).δ 1 (ComposableArrows.mk₂ f (pushout.inl f g))
        simp only [nerve.δ₁_mk₂_eq, pushout.condition]
        rfl)
  σ ≫ (discretePresheafInclusion 𝒞).val

/-- S8-3。単射に沿うとき、この 1 圏の押し出しそのものが ∞ 押し出しを与える。 -/
theorem discretePushout_isDiscrete {P Q R : 𝒞ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) [Mono f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (discretePushoutSquare f g) ∧
      ∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (discretePushoutSquare f g)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → Is0Truncated c.vertex := by
  sorry -- 点ごとの集合の単射は離散空間の cofibration。通常の押し出しでホモトピー押し出しを計算

/- 概要：S8-4：E 値の前層 O と空間値前層 F の切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。F ↦ Γ(F, O) は前層の余極限を極限に送る。
O の極限保存延長 O^ : PSh(𝒞)^op → E（HTT 5.1.5.6）と Γ(F, O) = O^(F)。
方針：元の圏 el(F)（F の Grothendieck 構成）上の極限。
規約：E 表示可能。
使われ方：Cor 8.12 の引き戻し。 -/
-- 集合値重みの sectionsOfDiagram・sectionsOfCone・sectionsOf・sectionsOf_map は
-- drafts/Sheaves/SetSections.lean に移動（S4 からも使うため、S8 の前に置く）。

/-- 普通の Yoneda 埋め込みの nerve（小さい始域だけを持ち上げる）。 -/
def liftedSetYoneda (𝒞 : Type u) [SmallCategory 𝒞] :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve 𝒞) ⟶ nerve (𝒞ᵒᵖ ⥤ Type u) where
  app _ := ↾fun x => (yoneda.mapComposableArrows _).obj x.down
  naturality := by sorry -- 合成可能射列の制限は Yoneda と可換

def oppositeSpaceYoneda (𝒞 : Type u) [SmallCategory 𝒞] :
    presheafShape 𝒞 ⟶ (PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).op :=
  (SSet.uliftFunctor.{u+1,u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := 𝒞)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve 𝒞)).hom ≫
    SSet.opFunctor.map (liftedSetYoneda 𝒞 ≫ (discretePresheafInclusion 𝒞).val)

/-- 空間値の重みの切断 O^ は Yoneda の反対に沿う O の点ごとの右 Kan 拡張。
離散重みの sectionsOf との比較は下で同じ選択から得る。 -/
def weightedSectionsData (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    Σ G : (PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).op ⟶ E,
      {ε : SSet.Homotopy (oppositeSpaceYoneda 𝒞 ≫ G) O // _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (oppositeSpaceYoneda 𝒞) O G ε} := by
  sorry -- HTT 5.1.5.6。各重みの元の ∞ 圏を添字に小極限を取る

abbrev weightedSections (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) := (weightedSectionsData O hE).1

def weightedSections_discrete (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (P : 𝒞ᵒᵖ ⥤ Type u)
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram P O)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm
      ((discretePresheafInclusion 𝒞).val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P)))) (sectionsOf P O hP) := by
  sorry -- 離散な重みの元の ∞ 圏は F.Elements の nerve。指定された二つの極限錐を比較

theorem weightedSections_discrete_map (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram P O)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram Q O)) :
    let e := (nerve.edgeMk φ).map (discretePresheafInclusion 𝒞).val
    let r := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
    Truncated.HomotopyCategory.homMk r ≫ (weightedSections_discrete O hE P hP).hom =
      (weightedSections_discrete O hE Q hQ).hom ≫ Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated := by
  sorry -- 元の圏の間の関手に沿う錐の制限は右 Kan 拡張の射と可換

/-- 一般の小さい ∞ 余極限に対する S8-4。余錐と全ての整合性を反転して O^ で送る。 -/
theorem sectionsOf_colimit (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) {K : SSet.{u}}
    {D : (SSet.uliftFunctor.{u+1,u}).obj K ⟶ PresheafCat 𝒞 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (weightedSections O hE) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c)) := by
  sorry -- Yoneda 上の右 Kan 拡張は重みの余極限を極限に送る（HTT 5.1.5.6）

/-- A6 に必要な集合値の場合。商の脚が Mono なので、指定した span の
押し出しを反転した cospan 上で切断が引き戻しを与える。 -/
theorem sectionsOf_pushout {P Q R : 𝒞ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) [Mono f]
    (O : Presheaf 𝒞 E) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (weightedSections O hE)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (discretePushoutSquare f g)))) := by
  sorry -- discretePushout_isDiscrete の余極限錐に S8-4。weightedSections_discrete が sectionsOf の脚と同定

-- sectionsOf_representable は SetSections.lean の指定錐比較を使う。

/-- 概要：S8-5：O が J 層（S1 の `IsSheaf`）なら Γ(−, O) はすべての J 局所同値を同値に送る。
方針：O^ の逆像の類は強飽和（O^ は極限を保つ）で、生成 sieve h_S ↪ h_c を含む（層条件）ので J 局所同値を含む（HTT 5.5.4.20 の筋）。
規約：—
使われ方：Cor 8.12。 -/
theorem sections_localEquiv_iso (J : GrothendieckTopology 𝒞) {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
    (O : Presheaf 𝒞 E) (hO : IsSheaf J O)
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram P O)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram Q O)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated := by
  sorry -- 基盤待ち：O^ の逆像の類は強飽和で生成 sieve を含む（HTT 5.5.4.20 の筋）

/-- 概要：S8-6：F の元の圏と同値な 1 圏 D（e : D ≌ F.Elements）があれば Γ(F, O) は D 上の極限（e に沿う制限は極限錐を保つ）。特に F_T = Hom(T, −) で D = Perfd_{T/}。
方針：同値に沿う制限と極限の不変性。
規約：`VertexIso`。
使われ方：A6 `sectionsOf_homSheaf_eq_perfectoidization`（A5 の `perfectoidization_isLimit` の錐と結ぶ）。 -/
def sectionsOf_eq_limit_elements (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram F O))
    {D : Type u} [SmallCategory D] (e : D ≌ F.Elements)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (e.functor ⋙ Functor.Elements.π F)) ≫ O))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (sectionsOf F O h) c.vertex := sorry

end SerrePositivity.InfinityCategories.Sheaves
