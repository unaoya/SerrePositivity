module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeHomotopyTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeTransportPrism
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定した自然変換が与える点ごとの錐・余錐による左右 Kan 拡張の定義。
方針：標準の比較錐を自然変換に沿って頂点を固定して輸送し、その極限性・余極限性を要求する。
規約：自然変換は関手単体集合の辺の表示である SSet.Homotopy。独立な点ごとの錐は入力にしない。
使われ方：Kerodon Def 7.3.1.2（Tag 02Y9）・Variant 7.3.1.5（Tag 02YC）。輸送の選択不変性・大域的一意性・存在は後続で証明する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 Kan 拡張の比較錐の指定自然変換に沿う輸送。
方針：標準錐から右図式のホモトピーを持ち上げ、頂点を全時間で固定する。
規約：時間は第二因子。family の終端が F₀ の制限上の合成錐を表す。
使われ方：Kerodon Def 7.3.1.2（Tag 02Y9） の α_c の具体的な合成の証拠。 -/
@[kerodon 02Y9]
structure RightKanConeTransport {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α : SSet.Homotopy (δ ≫ F) F₀) (c : C _⦋0⦌) where
  family : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ⊗ Δ[1] ⟶ D
  start : SSet.ι₀ ≫ family = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val
  diagram : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ▷ Δ[1]) ≫ family =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫ α.h
  fixedVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ▷ Δ[1]) ≫ family =
    fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val

/-- 概要：輸送の終端は元の図式 F₀ の制限上の錐。
方針：右因子の固定式を自然変換の終端で評価する。
規約：指定した自然変換の輸送から得る錐である。
使われ方：右 Kan 拡張の点ごとの極限性の検査。 -/
def RightKanConeTransport.cone {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌} (t : RightKanConeTransport δ F₀ F α c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c) :=
  ⟨SSet.ι₁ ≫ t.family, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (SSet.ι₁ ≫ t.family) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ≫ F₀
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, t.diagram,
      ← Category.assoc, SSet.ι₁_comp, Category.assoc, α.h₁]⟩

/-- 概要：右比較錐の輸送後も頂点は F(c)。
方針：左因子上の固定式を終端で評価する。
規約：頂点の厳密な等式。
使われ方：右 Kan 拡張の点ごとの値の公式。 -/
lemma RightKanConeTransport.cone_vertex {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D}
    {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) : t.cone.vertex = F.app _ c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (SSet.ι₁ ≫ t.family)) = _
  rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, t.fixedVertex, ← Category.assoc]
  change SSet.yonedaEquiv ((𝟙 (Δ[0] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val)) = _
  rw [Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone_vertex δ F c

/-- 概要：左 Kan 拡張の比較余錐の指定自然変換に沿う輸送。
方針：標準余錐からホモトピーを終端から持ち上げ、頂点を全時間で固定する。
規約：時間は第一因子。family の始端が F₀ の制限上の合成余錐を表す。
使われ方：Kerodon Variant 7.3.1.5（Tag 02YC） の β_c の具体的な合成の証拠。 -/
@[kerodon 02YC]
structure LeftKanCoconeTransport {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) (c : C _⦋0⦌) where
  family : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0] ⟶ D
  finish : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ family = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val
  diagram : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ family =
    (β_ (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫ β.h
  fixedVertex : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ family =
    snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val

/-- 概要：余錐の輸送の始端は元の図式 F₀ の制限上の余錐。
方針：左因子の固定式を自然変換の始端で評価する。
規約：指定した自然変換の輸送から得る余錐。
使われ方：左 Kan 拡張の点ごとの余極限性の検査。 -/
def LeftKanCoconeTransport.cocone {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌} (t : LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ t.family, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ t.family) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ≫ F₀
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, t.diagram,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, ← Category.assoc,
      SSet.ι₀_comp, Category.assoc, β.h₀]⟩

/-- 概要：左比較余錐の輸送後も頂点は F(c)。
方針：右因子上の固定式を始端で評価する。
規約：頂点の厳密な等式。
使われ方：左 Kan 拡張の点ごとの値の公式。 -/
lemma LeftKanCoconeTransport.cocone_vertex {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D}
    {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) : t.cocone.vertex = F.app _ c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ t.family)) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, t.fixedVertex,
    ← Category.assoc]
  change SSet.yonedaEquiv ((𝟙 (Δ[0] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val)) = _
  rw [Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone_vertex δ F c

/-- 概要：右比較錐の輸送は常に存在する。
方針：coslice の left fibration による、頂点固定の錐ホモトピー持ち上げを使う。
規約：標的 D のみ quasicategory を仮定する。
使われ方：比較錐の存在を Kan 拡張の極限性から切り離す。 -/
lemma rightKanConeTransport_nonempty {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α : SSet.Homotopy (δ ≫ F) F₀) (c : C _⦋0⦌) :
    Nonempty (RightKanConeTransport δ F₀ F α c) := by
  obtain ⟨G, hG, hGd, hGv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneHomotopy_extend
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫ α.h) (by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, α.h₀]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).property.symm)
  exact ⟨⟨G, hG, hGd, hGv⟩⟩

/-- 概要：左比較余錐の輸送は常に存在する。
方針：slice の right fibration による、終端からの頂点固定持ち上げを使う。
規約：指定した β の向きは F₀ → Fδ。
使われ方：余錐の存在を Kan 拡張の余極限性から切り離す。 -/
lemma leftKanCoconeTransport_nonempty {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) (c : C _⦋0⦌) :
    Nonempty (LeftKanCoconeTransport δ F₀ F β c) := by
  obtain ⟨G, hG, hGd, hGv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cocone_fixedVertex_prism
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val
    ((β_ (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫ β.h) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, ← Category.assoc,
        SSet.ι₁_comp, Category.assoc, β.h₁]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).property.symm)
  exact ⟨⟨G, hG, hGd, hGv⟩⟩

/-- 概要：指定自然変換が右 Kan 拡張を表す点ごとの条件。
方針：各 coslice の比較錐の合成を、頂点を固定した輸送で表し、その極限性を要求する。
規約：輸送は指定した α に両端と全時間で両立する。値だけの条件には置き換えない。
使われ方：Kerodon Def 7.3.1.2（Tag 02Y9）。選択不変性と大域的一意性は後続の定理。 -/
@[kerodon 02Y9]
def IsRightKanExtension {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α : SSet.Homotopy (δ ≫ F) F₀) : Prop :=
  ∀ c : C _⦋0⦌, ∃ t : RightKanConeTransport δ F₀ F α c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t.cone

/-- 概要：指定自然変換が左 Kan 拡張を表す点ごとの条件。
方針：各 slice の比較余錐の合成を、頂点を固定した輸送で表し、その余極限性を要求する。
規約：輸送は指定した β に両端と全時間で両立する。値だけの条件には置き換えない。
使われ方：Kerodon Variant 7.3.1.5（Tag 02YC）。選択不変性と大域的一意性は後続の定理。 -/
@[kerodon 02YC]
def IsLeftKanExtension {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) : Prop :=
  ∀ c : C _⦋0⦌, ∃ t : LeftKanCoconeTransport δ F₀ F β c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t.cocone

/-- 概要：右 Kan 拡張の各点の値は指定した slice 図式の極限の頂点。
方針：比較錐の極限性と頂点固定の等式を取り出す。
規約：自然性の組み立てや存在の逆方向は主張しない。
使われ方：点ごとの値の公式。 -/
lemma IsRightKanExtension.limitValue {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (h : IsRightKanExtension δ F₀ F α) (c : C _⦋0⦌) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t ∧ t.vertex = F.app _ c := by
  obtain ⟨t, ht⟩ := h c
  exact ⟨t.cone, ht, t.cone_vertex⟩

/-- 概要：左 Kan 拡張の各点の値は指定した slice 図式の余極限の頂点。
方針：比較余錐の余極限性と頂点固定の等式を取り出す。
規約：自然性の組み立てや存在の逆方向は主張しない。
使われ方：点ごとの値の公式。 -/
lemma IsLeftKanExtension.colimitValue {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (h : IsLeftKanExtension δ F₀ F β) (c : C _⦋0⦌) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t ∧ t.vertex = F.app _ c := by
  obtain ⟨t, ht⟩ := h c
  exact ⟨t.cocone, ht, t.cocone_vertex⟩

/-- 概要：同じ図式の二つの右 Kan 拡張の値は各点で同型。
方針：同じ slice 図式の二つの極限の一意性を使う。
規約：これは hD の同型であり、h Fun(C,D) の大域的同型は後続の課題。
使われ方：点ごとの一意性。 -/
def IsRightKanExtension.valueIso {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F G : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {β : SSet.Homotopy (δ ≫ G) F₀} (hF : IsRightKanExtension δ F₀ F α)
    (hG : IsRightKanExtension δ F₀ G β) (c : C _⦋0⦌) :
    (SSet.HomotopyCategory.mk (F.app _ c) : hoFunctor.obj D) ≅
      SSet.HomotopyCategory.mk (G.app _ c) := by
  let t := Classical.choose (hF.limitValue c)
  have ht := Classical.choose_spec (hF.limitValue c)
  let s := Classical.choose (hG.limitValue c)
  have hs := Classical.choose_spec (hG.limitValue c)
  exact ht.2 ▸ hs.2 ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso t s ht.1 hs.1

/-- 概要：同じ図式の二つの左 Kan 拡張の値は各点で同型。
方針：同じ slice 図式の二つの余極限の一意性を使う。
規約：hD の同型。大域的一意性をこの定理から直接推論しない。
使われ方：点ごとの一意性。 -/
def IsLeftKanExtension.valueIso {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F G : C ⟶ D} {α : SSet.Homotopy F₀ (δ ≫ F)}
    {β : SSet.Homotopy F₀ (δ ≫ G)} (hF : IsLeftKanExtension δ F₀ F α)
    (hG : IsLeftKanExtension δ F₀ G β) (c : C _⦋0⦌) :
    (SSet.HomotopyCategory.mk (F.app _ c) : hoFunctor.obj D) ≅
      SSet.HomotopyCategory.mk (G.app _ c) := by
  let t := Classical.choose (hF.colimitValue c)
  have ht := Classical.choose_spec (hF.colimitValue c)
  let s := Classical.choose (hG.colimitValue c)
  have hs := Classical.choose_spec (hG.colimitValue c)
  exact ht.2 ▸ hs.2 ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso t s ht.1 hs.1

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
