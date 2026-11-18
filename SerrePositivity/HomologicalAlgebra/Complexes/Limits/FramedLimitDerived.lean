module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.AdjointRightDerived
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitAdjunctionNormalization
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitNaturality

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

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：元の通常極限から局所化した計算関手への比較（Hovey §5.4）。
方針：同じ limitComparisonNatTrans を局所化し因子化同型の逆を合成する。
規約：元の図式の cofibrancy は不要。
使われ方：一般 homotopy 極限の右導来普遍性を持つ比較。 -/
def framedLimitDerivedComparison :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    lim ⋙ Q ⟶ (weakEquivalences (K ⥤ (Complex A))).Q ⋙ _root_.SerrePositivity.ComplexLimits.localizedFramedLimit A K := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.limitComparisonNatTrans A K) _ ≫
    (_root_.SerrePositivity.ComplexLimits.localizedFramedLimitComparison A K).inv

/-- 概要：元の比較は局所化随伴から得る導来比較に一致（Hovey §5.4）。
方針：元の極限錐を随伴の Hom 正規化へ代入する。
規約：同じ limitComparison を保持する。
使われ方：抽象的な Kan 拡張の普遍性を実際の比較へ移す。 -/
lemma framedLimitDerivedComparison_eq :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.comparison (constLimAdj (J := K)) Q
      (weakEquivalences (Complex A)) QD (_root_.SerrePositivity.ComplexLimits.framedLimitAdjunction A K)
        (_root_.SerrePositivity.ComplexLimits.localizedConstantDiagramComparison A K) = _root_.SerrePositivity.ComplexLimits.framedLimitDerivedComparison A K := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (Complex A)).Q
  let QD := (weakEquivalences (K ⥤ (Complex A))).Q
  apply NatTrans.ext
  funext F
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.comparison_app]
  change (_root_.SerrePositivity.ComplexLimits.framedLimitAdjunction A K).homEquiv (Q.obj (limit F)) (QD.obj F)
      ((_root_.SerrePositivity.ComplexLimits.localizedConstantDiagramComparison A K).hom.app (limit F) ≫ QD.map (limit.cone F).π) =
    Q.map (_root_.SerrePositivity.ComplexLimits.limitComparison A K F) ≫ (_root_.SerrePositivity.ComplexLimits.localizedFramedLimitComparison A K).inv.app F
  apply (cancel_mono ((_root_.SerrePositivity.ComplexLimits.localizedFramedLimitComparison A K).hom.app F)).1
  rw [Category.assoc, Iso.inv_hom_id_app]
  have h := _root_.SerrePositivity.ComplexLimits.framedLimitAdjunction_homEquiv_cone A K F (limit.cone F)
  exact h.trans (Category.comp_id _).symm

/-- 概要：具体的な計算関手は元の小極限の右導来関手（Hovey §5.4）。
方針：比較の一致と局所化随伴の左 Kan 拡張の普遍性を合成する。
規約：任意の小図式・任意の可換環で元の比較を使う。
使われ方：一般 homotopy 極限の導来普遍性。 -/
lemma localizedFramedLimit_isRightDerivedFunctor :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (_root_.SerrePositivity.ComplexLimits.localizedFramedLimit A K).IsRightDerivedFunctor (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedComparison A K)
      (weakEquivalences (K ⥤ (Complex A))) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  rw [← _root_.SerrePositivity.ComplexLimits.framedLimitDerivedComparison_eq A K]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived.isRightDerivedFunctor _ _ _ _ _ _ _

/-- 概要：通常の小極限の右導来関手が存在する（Hovey §5.4）。
方針：実際の局所化計算関手と元の比較の普遍性を使う。
規約：任意の可換環と小圏で成立する。
使われ方：一般 homotopy 極限の導来関手 API。 -/
lemma limitFunctor_hasRightDerivedFunctor :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    (lim ⋙ Q).HasRightDerivedFunctor (weakEquivalences (K ⥤ (Complex A))) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  have := _root_.SerrePositivity.ComplexLimits.localizedFramedLimit_isRightDerivedFunctor A K
  exact Functor.HasRightDerivedFunctor.mk' _ (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedComparison A K)

/-- 概要：同じ計算対象は任意の右導来極限の値と同型（Hovey §5.4）。
方針：局所化因子化同型と右導来関手の一意な比較同型を合成する。
規約：元の図式と重み付き end を置き換えない。
使われ方：一般 homotopy 極限の具体的な値の計算。 -/
def framedLimitDerivedIso (F : K ⥤ (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    ∀ (RF : (weakEquivalences (K ⥤ (Complex A))).Localization ⥤
        (weakEquivalences (Complex A)).Localization)
      (β : lim ⋙ Q ⟶ QD ⋙ RF),
      RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ (Complex A))) →
      (Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F) ≅ RF.obj (QD.obj F)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro RF β hRF
  have := hRF
  have := _root_.SerrePositivity.ComplexLimits.localizedFramedLimit_isRightDerivedFunctor A K
  exact ((_root_.SerrePositivity.ComplexLimits.localizedFramedLimitComparison A K).app F).symm ≪≫
    (Functor.rightDerivedUnique (_root_.SerrePositivity.ComplexLimits.localizedFramedLimit A K) RF (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedComparison A K)
      β (weakEquivalences (K ⥤ (Complex A)))).app
        ((weakEquivalences (K ⥤ (Complex A))).Q.obj F)

end SerrePositivity.ComplexLimits
