module

public import SerrePositivity.EInfinity.HomotopyWeight.PointwiseRealization
public import SerrePositivity.EInfinity.HomotopyWeight.TensorPiZero

/-!
# 射影重みを各値で実現した図式の余単体的 frame

概要：Hovey §5.4 の定値図式置換を図式圏の実際の frame へ拡張する。
方針：重みに標準単体をテンソルし、各値の実現と錐の随伴を合成する。
規約：図式の右類の評価での判定だけを使い、単体集合モデルは不要。
使われ方：定値図式からの局所化 Hom と始域 frame の重み付き錐の比較。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel
open scoped SSet.modelCategoryQuillen

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)

/-- 概要：単体集合を重みにテンソルし、各値を frame で実現する（Hovey §5.4）。
方針：構成済みの二つの左随伴を合成する。
規約：値は元の小図式圏。
使われ方：定値図式置換の標準 frame の構成。 -/
abbrev pointwiseTensorRealization : SSet.{u} ⥤ K ⥤ C :=
  WeightedCones.tensorDiagram K W ⋙ pointwiseRealization K B

/-- 概要：始域 frame の Hom 図式の実際の重み付き錐（Hovey §5.4）。
方針：各値の frame Hom の後で錐の右随伴を取る。
規約：すべての図式射に自然な単体集合の関手。
使われ方：図式の frame Hom の具体的な表示。 -/
abbrev pointwiseWeightedHom : (K ⥤ C) ⥤ SSet.{u} :=
  pointwiseFrameHom K B ⋙ WeightedCones.coneSpace K W

/-- 概要：各値のテンソル実現と重み付き Hom の随伴（Hovey §5.4）。
方針：テンソル図式と各値の実現の随伴を合成する。
規約：モデル構造の存在はこの随伴に不要。
使われ方：図式の標準 frame の Hom 同型。 -/
def pointwiseTensorAdjunction :
    pointwiseTensorRealization K W B ⊣ pointwiseWeightedHom K W B :=
  (WeightedCones.adjunction K W).comp (pointwiseRealizationAdjunction K B)

/-- 概要：各値のテンソル実現は実際の左随伴（Hovey §5.4）。
方針：構成済みの合成随伴を使う。
規約：余極限保存を追加仮定にはしない。
使われ方：標準単体の frame の境界表示。 -/
instance pointwiseTensorRealization_isLeftAdjoint :
    (pointwiseTensorRealization K W B).IsLeftAdjoint :=
  (pointwiseTensorAdjunction K W B).isLeftAdjoint

/-- 概要：重みの各値で実現した図式の標準 frame（Hovey §5.4）。
方針：標準単体をテンソル実現関手へ送る。
規約：元の重みと始域 frame を保持する。
使われ方：定値図式の導来 Hom の π₀ 比較。 -/
abbrev pointwiseTensorFrame : SimplexCategory ⥤ K ⥤ C :=
  SSet.stdSimplex ⋙ pointwiseTensorRealization K W B

/-- 概要：図式の標準 frame の Hom は始域 frame の重み付き錐（Hovey §5.4）。
方針：合成随伴の Hom 同型と標準単体の Yoneda 同型を使う。
規約：全単体と終域の図式射に自然な実際の同型。
使われ方：図式の局所化 Hom を重み付き錐で表示する。 -/
def pointwiseTensorFrameHomIso :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (pointwiseTensorFrame K W B) ≅ pointwiseWeightedHom K W B :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.homIso _ (pointwiseTensorAdjunction K W B)

/-- 概要：図式の標準 frame の零次は元の各値の重み実現（Hovey §5.4）。
方針：零単体のテンソル単位同型を各値の実現で送る。
規約：構成済みの定値図式置換と同じ対象。
使われ方：frame の π₀ 比較を元の置換図式へ移す。 -/
def pointwiseTensorFrameZeroIso :
    (pointwiseTensorFrame K W B).obj (SimplexCategory.mk 0) ≅
      (pointwiseRealization K B).obj W :=
  (pointwiseRealization K B).mapIso (zeroTensorWeightIso K W)

variable [ModelCategory C] [ModelCategory (K ⥤ C)]
  (hW : (boundaries K).rlp.llp (initial.to W))
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))
  (htriv : ∀ {F G : K ⥤ C} (p : F ⟶ G), trivialFibrations (K ⥤ C) p →
    ∀ k, trivialFibrations C (p.app k))

include hW hB htriv

/-- 概要：各値のテンソル実現は単射を図式の cofibration へ送る（Hovey §5.4）。
方針：自明 fibration の frame Hom と射影重みの境界持ち上げを使う。
規約：図式の cofibrancy を値ごとの条件へ弱めない。
使われ方：構成した図式 frame の Reedy cofibrancy。 -/
lemma pointwiseTensorRealization_map_mono {X Y : SSet.{u}} (i : X ⟶ Y) (hi : Mono i) :
    cofibrations (K ⥤ C) ((pointwiseTensorRealization K W B).map i) := by
  rw [← trivialFibrations_llp]
  intro F G p hp
  apply ((pointwiseTensorAdjunction K W B).hasLiftingProperty_iff i p).mpr
  apply SSet.rlp_monomorphisms.ge _ (coneSpace_map_boundary_rlp K W hW _ ?_) i hi
  intro k
  have : Fibration (p.app k) := ⟨(htriv p hp k).1⟩
  have : WeakEquivalence (p.app k) := ⟨(htriv p hp k).2⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_boundary_rlp B hB (p.app k)

/-- 概要：構成した図式の標準 frame は Reedy cofibrant（Hovey §5.4）。
方針：単射の cofibration 保存を標準単体の境界に適用する。
規約：単体集合のモデル構造は仮定しない。
使われ方：定値図式の導来 Hom の実際の frame。 -/
lemma pointwiseTensorFrame_reedyCofibrant :
    reedyLeft simplex (cofibrations (K ⥤ C)) (initial.to (pointwiseTensorFrame K W B)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.reedyCofibrant _ (pointwiseTensorRealization_map_mono K W B hW hB htriv)

omit htriv

variable (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
  (hfib : ∀ {F G : K ⥤ C} (p : F ⟶ G), Fibration p → ∀ k, Fibration (p.app k))

include hconst hfib

/-- 概要：各値のテンソル実現は anodyne を図式の自明 cofibration にする（Hovey §5.4）。
方針：各値の Kan fibration の Hom と重み付き錐の fibration 保存を使う。
規約：係数 frame の homotopical constancy を明示する。
使われ方：図式の標準 frame の homotopical constancy。 -/
lemma pointwiseTensorRealization_map_anodyne {X Y : SSet.{u}} (i : X ⟶ Y)
    (hi : SSet.anodyneExtensions i) :
    trivialCofibrations (K ⥤ C) ((pointwiseTensorRealization K W B).map i) := by
  rw [← fibrations_llp]
  intro F G p hp
  apply ((pointwiseTensorAdjunction K W B).hasLiftingProperty_iff i p).mpr
  have h : Fibration ((pointwiseWeightedHom K W B).map p) := by
    apply coneSpace_map_fibration K W hW
    intro k
    have : Fibration (p.app k) := hfib p ⟨hp⟩ k
    exact cosimplicialHom_fibration B hB hconst (p.app k)
  exact hi _ ((SSet.modelCategoryQuillen.fibration_iff _).mp h)

/-- 概要：図式の標準 frame の全単体作用素は弱同値（Hovey §5.4）。
方針：anodyne 保存と標準単体の実際の収縮を使う。
規約：値ごとの弱同値ではなく図式モデルの弱同値を得る。
使われ方：定値図式からの局所化 Hom を π₀ で計算する。 -/
lemma pointwiseTensorFrame_homotopicallyConstant {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences (K ⥤ C) ((pointwiseTensorFrame K W B).map f) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.homotopicallyConstant _
    (fun i hi => (pointwiseTensorRealization_map_anodyne K W B hW hB hconst hfib i hi).2) f

end SerrePositivity.EInfinity.HomotopyWeight
