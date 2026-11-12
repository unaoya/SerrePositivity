-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.SetSections。
-- S4・S8 共通の BS 側接続。基準 main 55b419a24（G2 先行分取り込み後）。ビルドしない。
-- F2 の重み付き切断 API を包むだけで、S8 の層化・局所同値には依存しない。
module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointConeLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointJoinNerveExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SimplexConeRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
-- 本ファイルは drafts/Sheaves/SheafCondition.lean を import する。

/-!
集合値重みの切断と、被覆篩による層条件との比較。
指定した極限錐を保持し、一般の重み射に関する G8 の自然性には依存しない。
証明本文は型検査前。SheafGenerators の承認済みの型へ、このファイルの比較を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
open _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories (IsPresentable)
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u + 1}} [Quasicategory E]

/-- 概要：Γ(F, O) の図式：F の元の圏 `F.Elements`（Mathlib `CategoryTheory.Functor.Elements`、射影 `Functor.Elements.π F : F.Elements ⥤ 𝒞ᵒᵖ`）の nerve を
持ち上げて O と合成したもの。
方針：S3 の `cechShape` と同じ持ち上げ。
規約：F は集合値（`𝒞ᵒᵖ ⥤ Type u`）、O は S1 の `Presheaf 𝒞 E`（= `presheafShape 𝒞 ⟶ E`、`presheafShape 𝒞` は nerve 𝒞ᵒᵖ の持ち上げ）。
使われ方：`sectionsOf`。 -/
def sectionsOfDiagram (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve F.Elements) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π F)) ≫ O

/-- 概要：E が表示可能なら上の図式は極限をもつ（添字は小さい）。 -/
theorem sectionsOfDiagram_hasLimit (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
    HasLimit (sectionsOfDiagram F O) := hE.hasLimit _

/-- 概要：S8-4：切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。選んだ極限錐の頂点。
方針：S2 の `globalSections` と同じ選び方。
規約：E 表示可能（`HasLimit` を引数で受ける）。
使われ方：Cor 8.12 の引き戻し。 -/
def sectionsOfCone (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) : JoinCone (sectionsOfDiagram F O) :=
  h.choose
def sectionsOf (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) : E _⦋0⦌ :=
  (sectionsOfCone F O h).vertex
theorem sectionsOfCone_isLimit (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : HasLimit (sectionsOfDiagram F O)) :
    IsLimitCone (sectionsOfCone F O h) := h.choose_spec

/-- 概要：Γ(−, O) の関手性：φ : P ⟶ Q に対し Γ(Q, O) → Γ(P, O)（元の圏の関手 P.Elements ⥤ Q.Elements に沿う制限と極限の普遍性）。
方針：錐の制限。
規約：E の辺。本体は IF-G2 の `SetWeight.sectionsMap φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit …)
  (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit …)`（Γ(Q) → Γ(P)、G2 停止点 1 で承認）
をそのまま使う。図式 `sectionsOfDiagram` は ∞ 側の `SetWeight.diagram` と同じ式（`Functor.Elements.π` の nerve を前合成）。
縦の比較は `SetWeight.tensorSpaceFunctor_setWeightHomNatural`。S4 は篩包含の場合の自然性だけを使い、
一般の φ の自然性は S8-5 用に待つ（IF-G2）。
使われ方：`sections_localEquiv_iso`、押し出しの比較。 -/
def sectionsOf_map {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf 𝒞 E)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
    SSet.Edge (sectionsOf Q O hQ) (sectionsOf P O hP) :=
  SetWeight.sectionsMap φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit P O hP)
    (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ)

/-! ## 篩の元の圏と S1 の添字圏 -/

/-- (V, f ∈ S) を Over U の対象と読む。射の向きは反転する。 -/
def sieveElementsToCategory {U : 𝒞} (S : Sieve U) :
    S.functor.Elements ⥤ (sieveCategory S)ᵒᵖ where
  obj x := Opposite.op ⟨Over.mk x.val.val, x.val.property⟩
  map f := (ObjectProperty.homMk
    (Over.homMk f.hom.unop (congrArg Subtype.val f.map_val))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- S1 の篩の対象を、篩前層の元と読む逆関手。 -/
def sieveCategoryToElements {U : 𝒞} (S : Sieve U) :
    (sieveCategory S)ᵒᵖ ⥤ S.functor.Elements where
  obj x := S.functor.elementsMk (Opposite.op x.unop.obj.left)
    ⟨x.unop.obj.hom, x.unop.property⟩
  map f := Functor.Elements.homMk f.unop.hom.left.op
    (Subtype.ext (Over.w f.unop.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 篩の元の圏は、S1 の Over の充満部分圏の反対圏と同値。 -/
def sieveElementsEquivalence {U : 𝒞} (S : Sieve U) :
    S.functor.Elements ≌ (sieveCategory S)ᵒᵖ where
  functor := sieveElementsToCategory S
  inverse := sieveCategoryToElements S
  unitIso := NatIso.ofComponents
    (fun x => Functor.Elements.isoMk (Iso.refl x.obj) (by rfl))
    (by intro x y f; ext; simp)
  counitIso := NatIso.ofComponents
    (fun x => (ObjectProperty.isoMk (Over.isoMk (Iso.refl _) (by simp))).op)
    (by intro x y f; apply Quiver.Hom.unop_inj; ext; simp)

/-- 同値は基底 𝒞ᵒᵖ への射影を保つ。 -/
lemma sieveCategoryToElements_comp_π {U : 𝒞} (S : Sieve U) :
    sieveCategoryToElements S ⋙ Functor.Elements.π S.functor = sieveDiagram S := rfl

/-- 包含を経由した表現可能前層の射影も同じ図式。 -/
lemma sieveCategoryToElements_inclusion_comp_π {U : 𝒞} (S : Sieve U) :
    sieveCategoryToElements S ⋙ S.functorInclusion.mapElements ⋙
      Functor.Elements.π (yoneda.obj U) = sieveDiagram S := rfl

/-- 篩上の切断図式と S1 の制限図式の、指定した添字変更での一致。 -/
lemma sieveSectionsDiagram_reindex {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S)) ≫
      sectionsOfDiagram S.functor F = restriction F S := by
  dsimp only [sectionsOfDiagram, restriction]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-! ## 表現可能前層の標準錐 -/

/-- Γ(h_U,F) を計算する錐の、𝒞ᵒᵖ での元になる錐。 -/
def representableElementsCone (U : 𝒞) : Cone (Functor.Elements.π (yoneda.obj U)) where
  pt := Opposite.op U
  π :=
    { app := fun x => x.val.op
      naturality := by
        intro x y f
        change 𝟙 (Opposite.op U) ≫ y.val.op = x.val.op ≫ f.hom
        rw [Category.id_comp, ← f.map_val]
        rfl }

/-- 標準錐の篩への制限は、S1 の錐そのもの。 -/
lemma representableElementsCone_sieve {U : 𝒞} (S : Sieve U) :
    (representableElementsCone U).whisker
      (sieveCategoryToElements S ⋙ S.functorInclusion.mapElements) = sieveCone S := by
  ext x <;> rfl

/-- F(U) を頂点とする、表現可能重み上の指定錐。 -/
def representableSectionsCone (U : 𝒞) (F : Presheaf 𝒞 E) :
    JoinCone (sectionsOfDiagram (yoneda.obj U) F) :=
  ((F1B.nerveCone (representableElementsCone U)).ulift).postcomp F

lemma representableSectionsCone_vertex (U : 𝒞) (F : Presheaf 𝒞 E) :
    (representableSectionsCone U F).vertex =
      F.app _ (ULift.up (nerveVertex (Opposite.op U))) := by
  rw [representableSectionsCone, JoinCone.vertex_postcomp,
    SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex, F1B.nerveCone_vertex]
  rfl

/-- 元の圏の始対象 (U,id) を、大きい宇宙の点として指定する。 -/
def representableSectionsInitialPoint (U : 𝒞) :
    (Δ[0] : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (yoneda.obj U).Elements) :=
  nervePoint (AsSmall.up.obj (Functor.Elements.initialYonedaObj U)) ≫
    (HomotopyLimits.nerveAsSmallIso (yoneda.obj U).Elements).inv

lemma representableSectionsInitialPoint_eq (U : 𝒞) :
    representableSectionsInitialPoint U = SSet.yonedaEquiv.symm
      (ULift.up (nerveVertex (Functor.Elements.initialYonedaObj U))) := by
  apply (cancel_mono (HomotopyLimits.nerveAsSmallIso (yoneda.obj U).Elements).hom).mp
  rw [representableSectionsInitialPoint, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, HomotopyLimits.nerveAsSmallIso_vertex]

/-- 始対象の点への制限は、サイズを上げても left anodyne。
AsSmall の通常圏に移してから既存の始対象定理を使う。 -/
lemma representableSectionsInitialPoint_leftAnodyne (U : 𝒞) :
    leftAnodyneExtensions (representableSectionsInitialPoint U) := by
  have hi : IsInitial (AsSmall.up.obj (Functor.Elements.initialYonedaObj U) :
      AsSmall.{u + 1} (yoneda.obj U).Elements) :=
    (Functor.Elements.isInitialYonedaObj U).isInitialObj AsSmall.up
  exact leftAnodyneExtensions.comp_mem _ _ (nervePoint_leftAnodyne hi)
    (MorphismProperty.of_isIso _ _)

/-- 恒等射の点への制限は、表現可能標準錐の全射として定値。
F を適用する前の nerve で両端と唯一の混合辺を照合する。 -/
lemma representableSectionsCone_point_val (U : 𝒞) (F : Presheaf 𝒞 E) :
    (restrictJoinCone (representableSectionsCone U F)
      (representableSectionsInitialPoint U)).val =
      SSet.const (F.app _ (ULift.up (nerveVertex (Opposite.op U)))) := by
  let c := (F1B.nerveCone (representableElementsCone U)).ulift
  have hc : joinMap (𝟙 _) (representableSectionsInitialPoint U) ≫ c.val =
      SSet.const (ULift.up (nerveVertex (Opposite.op U))) := by
    apply (cancel_mono (HomotopyLimits.nerveAsSmallIso 𝒞ᵒᵖ).hom).mp
    rw [SSet.const_comp]
    apply F2.Idempotent.pointJoinNerve_hom_ext
    · apply SSet.yonedaEquiv.injective
      change (HomotopyLimits.nerveAsSmallIso 𝒞ᵒᵖ).hom.app _ c.vertex = _
      rw [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex, F1B.nerveCone_vertex]
      rfl
    · apply SSet.yonedaEquiv.injective
      rw [representableSectionsInitialPoint_eq]
      rfl
    · rw [representableSectionsInitialPoint_eq]
      change (F1B.nerveCone (representableElementsCone U)).val.app (Opposite.op ⦋1⦌)
        (F1B.coneLegSimplex (Functor.Elements.initialYonedaObj U)) ⋙ AsSmall.up = _
      rw [F1B.nerveCone_leg]
      exact ComposableArrows.ext₁ rfl rfl rfl
  change joinMap (𝟙 _) (representableSectionsInitialPoint U) ≫ (c.val ≫ F) = _
  rw [← Category.assoc, hc, SSet.const_comp]

/-- 始対象 (U,id) の脚は恒等射なので、この指定錐が極限錐になる。 -/
lemma representableSectionsCone_isLimit (U : 𝒞) (F : Presheaf 𝒞 E) :
    IsLimitCone (representableSectionsCone U F) := by
  letI : Mono (representableSectionsInitialPoint U) := by
    unfold representableSectionsInitialPoint
    infer_instance
  apply (F2.isLimitCone_restrict_iff_of_leftAnodyne (representableSectionsCone U F)
    (representableSectionsInitialPoint U) (representableSectionsInitialPoint_leftAnodyne U)).mp
  exact F2.Idempotent.pointCone_isLimit_of_constant _ _ (representableSectionsCone_point_val U F)

/-- S8 の公開名を保持。選んだ極限錐と上の標準錐を、錐全体で比較する。 -/
def sectionsOf_representable (U : 𝒞) (F : Presheaf 𝒞 E)
    (h : HasLimit (sectionsOfDiagram (yoneda.obj U) F)) :
    VertexIso (sectionsOf (yoneda.obj U) F h)
      (F.app _ (ULift.up (nerveVertex (Opposite.op U)))) := by
  have e := limitVertexIso (sectionsOfCone (yoneda.obj U) F h)
    (representableSectionsCone U F) (sectionsOfCone_isLimit _ _ _)
    (representableSectionsCone_isLimit U F)
  simpa only [representableSectionsCone_vertex] using e

/-! ## 制限辺の可逆性と restrictionCone の極限性 -/

/-- 終錐への比較辺は、その頂点辺が可逆なとき、かつそのときだけ極限錐から来る。
右ファイブレーションの反映性を使うので、頂点の同型だけで錐を比較しない。 -/
lemma coneComparison_isInvertible_iff {K : SSet.{u + 1}} {p : K ⟶ E}
    (c d : JoinCone p) (hd : IsLimitCone d) (e : SSet.Edge (X := sliceOver p) c d) :
    IsInvertibleEdge (e.map (sliceOverProjection p)).toTruncated ↔ IsLimitCone c := by
  constructor
  · intro he
    have hi := derived_rightFibration_reflects_invertibleEdge
      (sliceOverProjection p) e.toTruncated he
    letI : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) := hi
    exact hd.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk e.toTruncated)).symm
  · intro hc
    have he : IsInvertibleEdge e.toTruncated :=
      isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
    exact he.map (sliceOverProjection p)

/-- G2 の指定錐から選んだ辺について、極限性の判定をそのまま適用する。 -/
lemma sectionsMap_isInvertible_iff {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (F : Presheaf 𝒞 E) (cP : JoinCone (sectionsOfDiagram P F)) (hcP : IsLimitCone cP)
    (cQ : JoinCone (sectionsOfDiagram Q F)) (hcQ : IsLimitCone cQ) :
    IsInvertibleEdge (SetWeight.sectionsMap φ F cP hcP cQ hcQ).toTruncated ↔
      IsLimitCone (SetWeight.restrictSectionsCone φ F cQ) := by
  simpa only [SetWeight.sectionsMap] using
    coneComparison_isInvertible_iff (SetWeight.restrictSectionsCone φ F cQ) cP hcP
      (SetWeight.sectionsConeMap φ F cP hcP cQ)

/-- 通常の全錐の添字変更は、nerve・宇宙持ち上げ・F による像と可換。 -/
lemma uliftNerveCone_whisker_val {I D : Type u} [SmallCategory I] [SmallCategory D]
    {G : I ⥤ 𝒞ᵒᵖ} (c : Cone G) (H : D ⥤ I) (F : Presheaf 𝒞 E) :
    (restrictJoinCone (((F1B.nerveCone c).ulift).postcomp F)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))).val =
      (((F1B.nerveCone (c.whisker H)).ulift).postcomp F).val := by
  change joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H)) ≫
    ((F1B.nerveCone c).ulift.val ≫ F) = _
  rw [← Category.assoc]
  change (restrictJoinCone ((F1B.nerveCone c).ulift)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))).val ≫ F = _
  rw [← HomotopyLimits.ulift_restrictJoinCone_val]
  change ((uliftConeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (joinMap (𝟙 _) (nerveMap H) ≫ (F1B.nerveCone c).val)) ≫ F = _
  rw [F1B.nerveCone_whisker]
  rfl

/-- 表現可能標準錐の篩への制限を元の圏の逆同値で引くと S1 の全錐になる。 -/
lemma sieveRestrictCanonicalCone_reindex_val {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E) :
    (restrictJoinCone
      (SetWeight.restrictSectionsCone S.functorInclusion F (representableSectionsCone U F))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S)))).val =
      (restrictionCone F S).val := by
  change joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (sieveCategoryToElements S))) ≫
      (joinMap (𝟙 _) (SetWeight.elementsMap S.functorInclusion) ≫
        (representableSectionsCone U F).val) = _
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp]
  dsimp only [SetWeight.elementsMap]
  rw [← Functor.map_comp]
  change (restrictJoinCone (representableSectionsCone U F)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sieveCategoryToElements S ⋙ S.functorInclusion.mapElements)))).val = _
  rw [representableSectionsCone, uliftNerveCone_whisker_val,
    representableElementsCone_sieve]
  rfl

/-- 表現可能側の任意の指定極限錐を制限しても、S1 の指定制限錐と同じ極限性を持つ。 -/
lemma sieveRestrictCone_isLimit_iff {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E)
    (cU : JoinCone (sectionsOfDiagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    IsLimitCone (SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
      IsLimitCone (restrictionCone F S) := by
  let c₀ := representableSectionsCone U F
  let i := SetWeight.elementsMap S.functorInclusion
  let e := (hoFunctor.map (sliceOverRestrict (sectionsOfDiagram (yoneda.obj U) F) i)).toFunctor.mapIso
    (limitConeIso cU c₀ hcU (representableSectionsCone_isLimit U F))
  have hchange : IsLimitCone (SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
      IsLimitCone (SetWeight.restrictSectionsCone S.functorInclusion F c₀) :=
    (F2.isLimitCone_iff_of_cone_val_eq _ (restrictJoinCone cU i) rfl).trans
      ((isLimitCone_iff_of_vertexIso e).trans
        (F2.isLimitCone_iff_of_cone_val_eq (restrictJoinCone c₀ i) _ rfl))
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S))
  have hj : IsQCatEquivalence j :=
    (F1B.nerveQCatEquivalence (sieveElementsEquivalence S).symm).isQCatEquivalence.ulift
  exact hchange.trans
    ((F2.Presentable.isLimitCone_iff_restrict_equivalentShape j hj
      (SetWeight.restrictSectionsCone S.functorInclusion F c₀)).trans
        (F2.isLimitCone_iff_of_cone_val_eq _ (restrictionCone F S)
          (sieveRestrictCanonicalCone_reindex_val S F)))

/-- S4 で使う篩包含の判定。任意の篩・任意の前層・指定された二つの極限錐。 -/
lemma sieveSectionsMap_isInvertible_iff {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E)
    (cS : JoinCone (sectionsOfDiagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (sectionsOfDiagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    IsInvertibleEdge (SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated ↔
      IsLimitCone (restrictionCone F S) :=
  (sectionsMap_isInvertible_iff S.functorInclusion F cS hcS cU hcU).trans
    (sieveRestrictCone_isLimit_iff S F cU hcU)

/-- 層条件は被覆篩に沿う sectionsOf_map の可逆性と同値。一般の重み射の自然性は不要。 -/
lemma isSheaf_iff_sieveSectionsMap_isInvertible (J : GrothendieckTopology 𝒞)
    (hE : IsPresentable E) (F : Presheaf 𝒞 E) :
    IsSheaf J F ↔ ∀ (U : 𝒞) (S : Sieve U), S ∈ J U →
      IsInvertibleEdge (sectionsOf_map S.functorInclusion F
        (sectionsOfDiagram_hasLimit hE S.functor F)
        (sectionsOfDiagram_hasLimit hE (yoneda.obj U) F)).toTruncated := by
  constructor
  · intro hF U S hS
    exact (sieveSectionsMap_isInvertible_iff S F _ (sectionsOfCone_isLimit _ _ _)
      _ (sectionsOfCone_isLimit _ _ _)).mpr (hF U S hS)
  · intro hF U S hS
    exact (sieveSectionsMap_isInvertible_iff S F _ (sectionsOfCone_isLimit _ _ _)
      _ (sectionsOfCone_isLimit _ _ _)).mp (hF U S hS)

end SerrePositivity.InfinityCategories.Sheaves
