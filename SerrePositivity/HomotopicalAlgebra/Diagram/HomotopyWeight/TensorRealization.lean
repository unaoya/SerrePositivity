module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameCones
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.StandardFrame

/-!
# 重み付き frame の標準単体による実現

概要：Hovey §5.4 の重み付き実現に標準単体をテンソルして実際の frame を構成する。
方針：重みのテンソルと実現の随伴を合成し、錐の持ち上げを使う。
規約：単体集合のモデル構造は不要で、同じ重みと係数 frame を保持する。
使われ方：重み付き錐空間と実現対象への局所化 Hom の比較。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel
open scoped _root_.SSet.modelCategoryQuillen

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

/-- 概要：単体集合を重みにテンソルしてから frame で実現する関手（Hovey §5.4）。
方針：実際の二つの左随伴を合成する。
規約：元の重み付き実現の対象を使う。
使われ方：重み付き錐の右随伴と標準 frame の構成。 -/
abbrev tensorRealization : SSet.{u} ⥤ C :=
  WeightedCones.tensorDiagram Kᵒᵖ W ⋙ FrameWeightRealization.functor K B

/-- 概要：テンソルした重みの実現と frame の錐の随伴（Hovey §5.4）。
方針：テンソル図式と実現の二つの随伴を合成する。
規約：右随伴は構成済みの同じ frameCone。
使われ方：標準 frame の Hom 同型と境界持ち上げ。 -/
def tensorRealizationAdjunction : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization K W B ⊣ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B :=
  (WeightedCones.adjunction Kᵒᵖ W).comp (FrameWeightRealization.adjunction K B)

instance tensorRealization_isLeftAdjoint : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization K W B).IsLeftAdjoint :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction K W B).isLeftAdjoint

variable (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))

include hW hB

/-- 概要：テンソルした重みの実現は単射を cofibration へ移す（Hovey §5.4）。
方針：錐が自明 fibration を境界の右類へ移すことを随伴で移す。
規約：重みの射影 cofibrancy と各 frame の Reedy cofibrancy を使う。
使われ方：構成する標準 frame の cofibrancy。 -/
lemma tensorRealization_map_mono {X Y : SSet.{u}} (i : X ⟶ Y) (hi : Mono i) :
    cofibrations C ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization K W B).map i) := by
  rw [← trivialFibrations_llp]
  intro X Y p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  apply ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction K W B).hasLiftingProperty_iff i p).mpr
  exact SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_target_boundary_rlp K W hW B hB p) i hi

/-- 概要：テンソルした重みの実現は anodyne を自明 cofibration へ移す（Hovey §5）。
方針：frame Hom の Kan fibration と錐の Kan fibration 保存を使う。
規約：係数 frame の全単体作用素は弱同値とする。
使われ方：構成する標準 frame の homotopical constancy。 -/
lemma tensorRealization_map_anodyne
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B.obj k).map f))
    {X Y : SSet.{u}} (i : X ⟶ Y) (hi : SSet.anodyneExtensions i) :
    trivialCofibrations C ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization K W B).map i) := by
  rw [← fibrations_llp]
  intro X Y p hp
  have : Fibration p := ⟨hp⟩
  apply ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction K W B).hasLiftingProperty_iff i p).mpr
  have h : Fibration ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).map p) := by
    apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_fibration Kᵒᵖ W hW
    intro k
    exact cosimplicialHom_fibration _ (hB k.unop) (hconst k.unop) p
  exact hi _ ((SSet.modelCategoryQuillen.fibration_iff _).mp h)

/-- 概要：重みに標準単体をテンソルした実際の frame（Hovey §5.4）。
方針：標準単体図式をテンソル実現関手で送る。
規約：係数と重みを選び直さない。
使われ方：重み付き錐の π₀ とモデル局所化 Hom の比較。 -/
abbrev tensorFrame : SimplexCategory ⥤ C := SSet.stdSimplex ⋙ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization K W B

/-- 概要：重み付き実現の標準 frame は Reedy cofibrant（Hovey §5.4）。
方針：標準単体の左随伴像の境界 cofibration を使う。
規約：単体集合のモデル構造を仮定しない。
使われ方：実際の frame Hom の局所化比較。 -/
lemma tensorFrame_reedyCofibrant :
    reedyLeft simplex (cofibrations C) (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.reedyCofibrant _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization_map_mono K W B hW hB)

/-- 概要：重み付き実現の標準 frame は homotopically constant（Hovey §5.4）。
方針：anodyne 保存と標準単体の収縮を使う。
規約：各係数 frame の全単体作用素の弱同値性を使う。
使われ方：重み付き錐の連結成分の Hom 比較。 -/
lemma tensorFrame_homotopicallyConstant
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B.obj k).map f))
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B).map f) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.homotopicallyConstant _
    (fun i hi => (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealization_map_anodyne K W B hW hB hconst i hi).2) f

omit hW hB

/-- 概要：構成した frame の Hom は元の重み付き錐と同型（Hovey §5.4）。
方針：テンソル実現の随伴と標準単体の Yoneda 同型を使う。
規約：全単体と終域の射で自然な実際の同型。
使われ方：重み付き錐空間の π₀ を局所化 Hom へ移す。 -/
def tensorFrameHomIso : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B) ≅ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.homIso _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction K W B)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
