module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.AdjointRightDerived
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitAdjunctionNormalization
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitNaturality

/-!
# 元の極限比較を持つ具体的な homotopy 極限の右導来普遍性

概要：BM 命題 4.1・Hovey §5.4 の一般小図式の計算関手を右導来極限と証明する。
方針：局所化随伴の自然変換の普遍性と元の極限錐の正規化を合成する。
規約：同じ重み付き end と元の limitComparisonNatTrans を保持する。
使われ方：E2a-4 の一般 homotopy 極限と任意の右導来関手との比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：元の通常極限から局所化した計算関手への比較（Hovey §5.4）。
方針：同じ limitComparisonNatTrans を局所化し因子化同型の逆を合成する。
規約：元の図式の cofibrancy は不要。
使われ方：一般 homotopy 極限の右導来普遍性を持つ比較。 -/
def framedLimitDerivedComparison :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    lim ⋙ Q ⟶ (weakEquivalences (K ⥤ (operad A).Algebra)).Q ⋙ localizedFramedLimit A K := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  exact Functor.whiskerRight (limitComparisonNatTrans A K) _ ≫
    (localizedFramedLimitComparison A K).inv

/-- 概要：元の比較は局所化随伴から得る導来比較に一致（Hovey §5.4）。
方針：元の極限錐を随伴の Hom 正規化へ代入する。
規約：同じ limitComparison を保持する。
使われ方：抽象的な Kan 拡張の普遍性を実際の比較へ移す。 -/
lemma framedLimitDerivedComparison_eq :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.comparison (constLimAdj (J := K)) Q
      (weakEquivalences (operad A).Algebra) QD (framedLimitAdjunction A K)
        (localizedConstantDiagramComparison A K) = framedLimitDerivedComparison A K := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  let Q := (weakEquivalences (operad A).Algebra).Q
  let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
  apply NatTrans.ext
  funext F
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.comparison_app]
  change (framedLimitAdjunction A K).homEquiv (Q.obj (limit F)) (QD.obj F)
      ((localizedConstantDiagramComparison A K).hom.app (limit F) ≫ QD.map (limit.cone F).π) =
    Q.map (limitComparison A K F) ≫ (localizedFramedLimitComparison A K).inv.app F
  apply (cancel_mono ((localizedFramedLimitComparison A K).hom.app F)).1
  rw [Category.assoc, Iso.inv_hom_id_app]
  have h := framedLimitAdjunction_homEquiv_cone A K F (limit.cone F)
  exact h.trans (Category.comp_id _).symm

/-- 概要：具体的な計算関手は元の小極限の右導来関手（Hovey §5.4）。
方針：比較の一致と局所化随伴の左 Kan 拡張の普遍性を合成する。
規約：任意の小図式・任意の可換環で元の比較を使う。
使われ方：一般 homotopy 極限の導来普遍性。 -/
lemma localizedFramedLimit_isRightDerivedFunctor :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    (localizedFramedLimit A K).IsRightDerivedFunctor (framedLimitDerivedComparison A K)
      (weakEquivalences (K ⥤ (operad A).Algebra)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  rw [← framedLimitDerivedComparison_eq A K]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.isRightDerivedFunctor _ _ _ _ _ _ _

/-- 概要：通常の小極限の右導来関手が存在する（Hovey §5.4）。
方針：実際の局所化計算関手と元の比較の普遍性を使う。
規約：任意の可換環と小圏で成立する。
使われ方：一般 homotopy 極限の導来関手 API。 -/
lemma limitFunctor_hasRightDerivedFunctor :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    (lim ⋙ Q).HasRightDerivedFunctor (weakEquivalences (K ⥤ (operad A).Algebra)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  have := localizedFramedLimit_isRightDerivedFunctor A K
  exact Functor.HasRightDerivedFunctor.mk' _ (framedLimitDerivedComparison A K)

/-- 概要：同じ計算対象は任意の右導来極限の値と同型（Hovey §5.4）。
方針：局所化因子化同型と右導来関手の一意な比較同型を合成する。
規約：元の図式と重み付き end を置き換えない。
使われ方：一般 homotopy 極限の具体的な値の計算。 -/
def framedLimitDerivedIso (F : K ⥤ (operad A).Algebra) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    ∀ (RF : (weakEquivalences (K ⥤ (operad A).Algebra)).Localization ⥤
        (weakEquivalences (operad A).Algebra).Localization)
      (β : lim ⋙ Q ⟶ QD ⋙ RF),
      RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ (operad A).Algebra)) →
      (Q.obj ((framedLimitFunctor A K).obj F) ≅ RF.obj (QD.obj F)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro RF β hRF
  have := hRF
  have := localizedFramedLimit_isRightDerivedFunctor A K
  exact ((localizedFramedLimitComparison A K).app F).symm ≪≫
    (Functor.rightDerivedUnique (localizedFramedLimit A K) RF (framedLimitDerivedComparison A K)
      β (weakEquivalences (K ⥤ (operad A).Algebra))).app
        ((weakEquivalences (K ⥤ (operad A).Algebra)).Q.obj F)

end SerrePositivity.EInfinity.BarrattEccles
