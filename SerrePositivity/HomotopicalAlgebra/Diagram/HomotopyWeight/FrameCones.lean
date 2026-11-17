module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeLifting
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SourceInvariance
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.PointwiseBrown
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
# Frame の図式の重み付き Kan 錐

概要：Hovey §5 の frame Hom の重み付き錐に Kan 性と比較の不変性を与える。
方針：各頂点の frame の持ち上げを射影 cofibrant 重みで束ねる。
規約：重みは実際の射影境界の左類で、単体集合モデルは仮定しない。
使われ方：E 代数の重み付き右 frame の end の Hom 比較。
-/

@[expose] public section

noncomputable section

universe u v w t

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))

/-- 概要：frame の図式からの重み付き写像空間（Hovey §5）。
方針：頂点ごとの cosimplicial Hom の図式の錐空間を取る。
規約：実現の随伴の右関手と同じ Hom の図式を使う。
使われ方：一般 homotopy 極限の写像空間の比較。 -/
abbrev frameCone (B : K ⥤ SimplexCategory ⥤ C) : C ⥤ SSet.{u} :=
  FrameWeightRealization.hom K B ⋙ WeightedCones.coneSpace Kᵒᵖ W

include hW

/-- 概要：frame の重み付き錐は自明 fibration を境界の右類へ移す（Hovey §5）。
方針：各頂点の Reedy cofibrancy による境界持ち上げを束ねる。
規約：図式の始域の cofibrancy は追加せず、各 frame の条件を明示する。
使われ方：終域に関する Brown 不変性の入力。 -/
lemma frameCone_target_boundary_rlp (B : K ⥤ SimplexCategory ⥤ C)
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).map p) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_boundary_rlp Kᵒᵖ W hW
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_boundary_rlp (B.obj k.unop) (hB k.unop) p

/-- 概要：frame の重み付き錐は fibrant 終域で Kan 複体（Hovey §5）。
方針：各 frame の Hom の Kan 性を重み付き錐へ移す。
規約：frame は Reedy cofibrant かつ homotopically constant とする。
使われ方：重み付き end を検出する Kan 写像空間。 -/
lemma frameCone_kanComplex (B : K ⥤ SimplexCategory ⥤ C)
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B.obj k).map f)) (Y : C) [IsFibrant Y] :
    SSet.KanComplex ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).obj Y) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_kanComplex Kᵒᵖ W hW
  intro k
  exact cosimplicialHom_kanComplex _ (hB k.unop) (hconst k.unop) Y

/-- 概要：frame の自明 cofibration の重み付き Hom は境界の右類（Hovey §5）。
方針：各頂点の相対境界持ち上げを射影 cofibrant 重みで束ねる。
規約：元の frame の自然変換が誘導する錐の射を使う。
使われ方：一般 homotopy 極限の係数 frame の比較。 -/
lemma frameCone_source_boundary_rlp {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (ha : ∀ k, reedyLeft simplex (trivialCofibrations C) (a.app k))
    (Y : C) [IsFibrant Y] :
    SSet.modelCategoryQuillen.I.rlp
      ((WeightedCones.coneSpace Kᵒᵖ W).map
        (((FrameWeightRealization.homFamily K).map a.op).app Y)) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_boundary_rlp Kᵒᵖ W hW
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_boundary_rlp (a.app k.unop) (ha k.unop) Y

variable {D : Type w} [Category.{t} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：重み付き frame Hom は fibrant 終域の弱同値を反転する（Hovey §5）。
方針：自明 fibration の境界持ち上げと Brown 分解を使う。
規約：反転先は任意の anodyne を反転する関手でよい。
使われ方：一般 homotopy 極限の Hom 比較の終域不変性。 -/
lemma frameCone_target_weakEquivalence_isIso (B : K ⥤ SimplexCategory ⥤ C)
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    IsIso (L.map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).map f)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.map_isIso_of_fibrant (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B ⋙ L)
  intro Y Z p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  exact _root_.SerrePositivity.SimplicialModel.MonoRightLiftingContraction.image_isIso _
    (SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_target_boundary_rlp K W hW B hB p)) L hL

/-- 概要：frame の自明 cofibration は重み付き Hom で反転される（Hovey §5）。
方針：重み付き Hom の境界の右類から具体的な切断と収縮を取る。
規約：終域は fibrant、反転先に単体集合のモデル構造を要求しない。
使われ方：係数 frame の Brown 分解の比較射。 -/
lemma frameCone_source_trivialCofibration_isIso {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (ha : ∀ k, reedyLeft simplex (trivialCofibrations C) (a.app k))
    (Y : C) [IsFibrant Y] :
    IsIso (L.map ((WeightedCones.coneSpace Kᵒᵖ W).map
      (((FrameWeightRealization.homFamily K).map a.op).app Y))) :=
  _root_.SerrePositivity.SimplicialModel.MonoRightLiftingContraction.image_isIso _
    (SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_source_boundary_rlp K W hW a ha Y)) L hL

/-- 概要：cofibrant frame の頂点ごとの弱同値は重み付き Hom で反転される。
方針：関手的 Reedy 分解から図式全体の Brown 分解を作る（Hovey §5）。
規約：図式の射影 cofibrancy は不要、元の圏の関手的分解を明示する。
使われ方：一般 homotopy 極限の係数 frame の弱同値不変性。 -/
lemma frameCone_source_weakEquivalence_isIso
    (fact : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    {B B' : K ⥤ SimplexCategory ⥤ C} (a : B ⟶ B')
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    (hB' : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B'.obj k)))
    (ha : ∀ k n, weakEquivalences C ((a.app k).app n))
    (target : C) [IsFibrant target] :
    IsIso (L.map ((WeightedCones.coneSpace Kᵒᵖ W).map
      (((FrameWeightRealization.homFamily K).map a.op).app target))) := by
  let := simplexModelCategory C
  let d := FunctorFactorizationSequence.functorialFactorizationData simplex
    (fun _ _ h => SimplexCategory.ext h) (fun n => ⟨SimplexCategory.mk n, rfl⟩) fact
  let d' : MorphismProperty.FunctorialFactorizationData
      (cofibrations (SimplexCategory ⥤ C)) (trivialFibrations (SimplexCategory ⥤ C)) :=
    d.ofLE (by rfl) (reedyRight_trivialFibrations_eq simplex).le
  let T : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ D :=
    FrameWeightRealization.homFamily K ⋙
      (CategoryTheory.evaluation C (Kᵒᵖ ⥤ SSet.{u})).obj target ⋙
      WeightedCones.coneSpace Kᵒᵖ W ⋙ L
  apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.map_isIso_of_pointwise_cofibrant K d' T _ a
    (fun k => ⟨hB k⟩) (fun k => ⟨hB' k⟩) ha
  intro B₀ B₁ b hb
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_source_trivialCofibration_isIso K W hW L hL b _ target
  intro k
  exact (reedyLeft_trivialCofibrations_iff simplex (b.app k)).mpr (hb k)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
