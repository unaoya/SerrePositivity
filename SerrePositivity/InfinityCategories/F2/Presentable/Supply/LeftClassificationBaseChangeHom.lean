module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.NormalizedHomNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.LeftClassificationBaseChangeEdges

/-!
概要：元の実全空間射の分類 Hom は、元の底変換の指定同型と可換。
方針：全分類の底変換同型の自然性を正規化し、実比較辺の底変換則を代入する。
規約：実際の fiberComparisonBaseChange と既存の指定底変換同型を使う。
使われ方：P-12 の coslice の実 Hom 制限を指定単位の Hom 普遍性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：元の図式間の射を元の始域の射で前合成する。
方針：内部前合成の Hom 作用を元の両図式の頂点へ正規化する。
規約：任意の単体集合を許す。使われ方：分類した指定射の底の制限。 -/
def precomposeFunctorHom {A B X : SSet.{u}} (k : B ⟶ A) {F G : A ⟶ X}
    (α : FunctorHom F G) : FunctorHom (k ≫ F) (k ≫ G) :=
  normalizedVertexHomMap ((pre k).app X) (x := functorVertex F) (y := functorVertex G)
    (x' := functorVertex (k ≫ F)) (y' := functorVertex (k ≫ G)) rfl rfl α

/-- 概要：分類の底変換の始点を元の制限図式の頂点へ同定する。
方針：元の分類の頂点等式を内部前合成へ送る。
規約：既存の底変換同型と同じ等式。使われ方：正規化した自然性の始点。 -/
lemma leftClassificationBaseChange_sourceEq
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}).app
          (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) :=
  congrArg (((pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}).app
    (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)

/-- 概要：分類の底変換の終点を元の引き戻しの分類図式の頂点へ同定する。
方針：実底変換の頂点の式と元の分類の頂点等式を合成する。
規約：元の通常の引き戻しを使う。使われ方：正規化した自然性の終点。 -/
lemma leftClassificationBaseChange_targetEq
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    functorVertex (leftStraighteningInfinityDiagram (pullback.snd p k)) =
      (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D).app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) :=
  ((congrArg ((leftStraighteningInfinityMap D).app (Opposite.op ⦋0⦌))
    (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p))).trans
      (leftStraighteningInfinityDiagram_vertex (pullback.snd p k)).symm).symm

/-- 概要：正規化した全底変換同型の成分は、既存の同じ分類図式の底変換同型。
方針：元の同型の定義と指定端点等式を展開する。
規約：同型を選び直さない。使われ方：全自然性を元の実分類 Hom の正方形へ移す。 -/
lemma leftClassificationBaseChange_component
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    normalizedFunctorIsoComponent (leftStraighteningInfinityMap_baseChangeIso k)
      (leftFibrationInfinityVertex p) (leftClassificationBaseChange_sourceEq p k)
      (leftClassificationBaseChange_targetEq p k) =
        leftStraighteningInfinityDiagram_baseChangeIso p k := by
  rfl

/-- 概要：元の実全空間射の分類と底変換は、既存の指定同型による正方形で可換。
方針：全分類の底変換同型の自然性を、元の比較辺の底変換則で正規化する。
規約：同じ分類 Hom と同じ実引き戻し比較を使う。
使われ方：coslice の Hom 制限の全単射性を指定した分類射へ移す主正方形。 -/
lemma leftClassificationHom_baseChange
    {E H B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (k : D ⟶ B) :
    precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (leftClassificationHom p q f hf) ≫
        (leftStraighteningInfinityDiagram_baseChangeIso q k).hom =
      (leftStraighteningInfinityDiagram_baseChangeIso p k).hom ≫
        leftClassificationHom (pullback.snd p k) (pullback.snd q k)
          (fiberComparisonBaseChange p q f hf k)
          (fiberComparisonBaseChange_projection p q f hf k) := by
  let α := Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  have h := normalizedVertexHomMap_naturality (leftStraighteningInfinityMap_baseChangeIso k)
    (leftClassificationBaseChange_sourceEq p k) (leftClassificationBaseChange_sourceEq q k)
    (leftClassificationBaseChange_targetEq p k) (leftClassificationBaseChange_targetEq q k) α
  rw [leftClassificationBaseChange_component, leftClassificationBaseChange_component] at h
  have hL : normalizedVertexHomMap (leftStraighteningInfinityMap B ≫ P)
      (leftClassificationBaseChange_sourceEq p k) (leftClassificationBaseChange_sourceEq q k) α =
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (leftClassificationHom p q f hf) := by
    rw [leftClassificationHom_eq_normalizedMap]
    exact (normalizedVertexHomMap_comp (leftStraighteningInfinityMap B) P
      (leftStraighteningInfinityDiagram_vertex p) (leftStraighteningInfinityDiagram_vertex q)
      rfl rfl α).symm
  have hR : normalizedVertexHomMap
      (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D)
      (leftClassificationBaseChange_targetEq p k) (leftClassificationBaseChange_targetEq q k) α =
      leftClassificationHom (pullback.snd p k) (pullback.snd q k)
        (fiberComparisonBaseChange p q f hf k)
        (fiberComparisonBaseChange_projection p q f hf k) := by
    rw [leftClassificationHom_eq_normalizedMap]
    have hc := normalizedVertexHomMap_comp (leftFibrationInfinityBaseChange k)
      (leftStraighteningInfinityMap D)
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p)).symm
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf q)).symm
      (leftStraighteningInfinityDiagram_vertex (pullback.snd p k))
      (leftStraighteningInfinityDiagram_vertex (pullback.snd q k)) α
    rw [leftFibrationBaseChange_normalizedHom] at hc
    exact hc.symm
  rw [hL, hR] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
