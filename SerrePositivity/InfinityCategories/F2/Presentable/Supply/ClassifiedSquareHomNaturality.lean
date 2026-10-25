module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.LeftClassificationBaseChangeHom

/-!
概要：異なる底の間の実可換正方形を分類し、その分類の自然性を証明する。
方針：正方形を実 pullback へ持ち上げ、分類の合成則と指定底変換正方形を使う。
規約：元の全空間射と指定底変換同型を保持する。
使われ方：P-12 の coslice と始点固定 twisted arrow の指定単位の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance supplyClassifiedSquareHomNaturality_pullbackLeftFibration
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：異なる底の間の実正方形を元の全分類図式間の射へ移す。
方針：実 pullback への持ち上げを分類し、指定底変換同型の逆を合成する。
規約：元の f とその可換条件を使う。使われ方：共同 Hom の始点固定の指定単位。 -/
def leftClassificationSquareHom {A C E H : SSet.{u}}
    [Quasicategory A] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ C) [LeftFibration p] [LeftFibration q]
    (k : A ⟶ C) (f : E ⟶ H) (hf : f ≫ q = p ≫ k) :
    FunctorHom (leftStraighteningInfinityDiagram p)
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram q) :=
  leftClassificationHom p (pullback.snd q k) (pullback.lift f p hf)
    (pullback.lift_snd _ _ _) ≫ (leftStraighteningInfinityDiagram_baseChangeIso q k).inv

/-- 概要：実正方形の持ち上げと底上の全空間射の合成は、同じ底変換射で可換。
方針：pullback の両射影で検出する。
規約：元の可換正方形の厳密な等式を使う。使われ方：分類前の指定比較の自然性。 -/
lemma squareLift_baseChange_naturality {A C E E' H H' : SSet.{u}}
    (p : E ⟶ A) (p' : E' ⟶ A) (q : H ⟶ C) (q' : H' ⟶ C)
    (k : A ⟶ C) (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : E' ⟶ H') (hg : g ≫ q' = p' ≫ k)
    (v : E ⟶ E') (hv : v ≫ p' = p) (w : H ⟶ H') (hw : w ≫ q' = q)
    (hsq : v ≫ g = f ≫ w) :
    v ≫ pullback.lift g p' hg =
      pullback.lift f p hf ≫ fiberComparisonBaseChange q q' w hw k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, fiberComparisonBaseChange_fst]
    rw [← Category.assoc, pullback.lift_fst]
    exact hsq
  · simp only [Category.assoc, pullback.lift_snd, fiberComparisonBaseChange_projection]
    exact hv

/-- 概要：実正方形の分類は、底上の全空間比較に関して自然。
方針：指定底変換正方形を打ち消し、元の実持ち上げの可換性を分類の合成則へ渡す。
規約：元の指定分類射の等式。使われ方：coslice 単位から共同 Hom 単位への移送。 -/
lemma leftClassificationSquareHom_naturality {A C E E' H H' : SSet.{u}}
    [Quasicategory A] [Quasicategory C]
    (p : E ⟶ A) (p' : E' ⟶ A) (q : H ⟶ C) (q' : H' ⟶ C)
    [LeftFibration p] [LeftFibration p'] [LeftFibration q] [LeftFibration q']
    (k : A ⟶ C) (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : E' ⟶ H') (hg : g ≫ q' = p' ≫ k)
    (v : E ⟶ E') (hv : v ≫ p' = p) (w : H ⟶ H') (hw : w ≫ q' = q)
    (hsq : v ≫ g = f ≫ w) :
    leftClassificationHom p p' v hv ≫ leftClassificationSquareHom p' q' k g hg =
      leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationHom q q' w hw) := by
  have hn : (leftStraighteningInfinityDiagram_baseChangeIso q k).inv ≫
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (leftClassificationHom q q' w hw) =
      leftClassificationHom (pullback.snd q k) (pullback.snd q' k)
        (fiberComparisonBaseChange q q' w hw k)
        (fiberComparisonBaseChange_projection q q' w hw k) ≫
          (leftStraighteningInfinityDiagram_baseChangeIso q' k).inv := by
    apply (cancel_mono (leftStraighteningInfinityDiagram_baseChangeIso q' k).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [leftClassificationHom_baseChange q q' w hw k, Iso.inv_hom_id_assoc]
  unfold leftClassificationSquareHom
  simp only [Category.assoc]
  rw [hn]
  simp only [← Category.assoc, leftClassificationHom_comp,
    squareLift_baseChange_naturality p p' q q' k f hf g hg v hv w hw hsq]

/-- 概要：底上の元の前合成同値を分類した指定射は可逆。
方針：元の可逆な coherent 辺を分類し、両端点の正規化を同型で共役する。
規約：別の同型の存在で代用せず、元の分類射の可逆性を結論する。
使われ方：実 coslice 比較の分類による指定単位の普遍性の移送。 -/
lemma leftClassificationHom_isIso_of_precompositionEquivalence
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsIso (leftClassificationHom p q f hf) := by
  rw [leftClassificationHom_eq_normalizedMap]
  have : IsIso (Truncated.HomotopyCategory.homMk
      (leftFibrationInfinityEdge p q f hf).toTruncated) :=
    leftFibrationInfinityEdge_isInvertible_of_precompositionEquivalence p q f hf ef
  unfold leftClassificationNormalizedMap normalizedVertexHomMap
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable
