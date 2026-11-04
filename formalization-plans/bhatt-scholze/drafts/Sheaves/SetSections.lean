-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.SetSections。
-- S4・S8 共通の BS 側接続。基準 main 9f59541d3。ビルドしない。
-- F2 の重み付き切断 API を包むだけで、S8 の層化・局所同値には依存しない。
module

public import SerrePositivity.InfinityCategories.F2.Tensor.SetSections
public import SerrePositivity.InfinityCategories.Core.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
-- 要確認（IF-G2：先行分は math/g2 に実在、main 取り込み待ち）：
-- public import SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
-- 本ファイルは drafts/Sheaves/SheafCondition.lean を import する。

/-!
集合値重みの切断と、被覆篩による層条件との比較。
指定した極限錐を保持し、一般の重み射に関する G8 の自然性には依存しない。
証明本文を記述した箇所も型検査前。残る幾何的比較は個別の sorry に分離する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
open F2.Presentable (IsPresentable)
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
theorem sectionsOfDiagram_hasLimit (hE : F2.Presentable.IsPresentable E) (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
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
  simp only [sectionsOfDiagram, restriction, ← Category.assoc, ← Functor.map_comp,
    ← nerveMap_comp, sieveCategoryToElements_comp_π]

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
    SerrePositivity.InfinityCategories.JoinCone.ulift_vertex, F1B.nerveCone_vertex]
  rfl

/-- 始対象 (U,id) の脚は恒等射なので、この指定錐が極限錐になる。 -/
lemma representableSectionsCone_isLimit (U : 𝒞) (F : Presheaf 𝒞 E) :
    IsLimitCone (representableSectionsCone U F) := by
  -- Functor.Elements.isInitialYonedaObj U と nervePoint_leftAnodyne を使う。
  -- ulift 後も始対象の点への制限が left anodyne。錐のその脚は F(id)=id。
  -- IsLimitCone の制限判定で sliceIdentityCone の終対象性へ帰着する。
  sorry

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

/-- 表現可能側の任意の指定極限錐を制限しても、S1 の指定制限錐と同じ極限性を持つ。 -/
lemma sieveRestrictCone_isLimit_iff {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E)
    (cU : JoinCone (sectionsOfDiagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    IsLimitCone (SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
      IsLimitCone (restrictionCone F S) := by
  -- 1. limitConeIso cU (representableSectionsCone U F) hcU
  --      (representableSectionsCone_isLimit U F) を sliceOverRestrict で送る。
  --    必要なのは錐の圏での同型であり、sectionsOf_representable の頂点同型だけでは足りない。
  -- 2. sieveElementsEquivalence S の inverse の nerve（ulift）で制限する。
  --    F2.Presentable.isLimitCone_iff_restrict_equivalentShape で極限性を移す。
  -- 3. F1B.nerveCone_whisker、representableElementsCone_sieve と ulift の自然性で
  --    制限された全錐を restrictionCone F S と同定する。
  sorry

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
