module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitConePiZeroSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitHomSource

/-!
# 定値図式と具体的な極限計算対象の導来 Hom 同値の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の導来 Hom の同値は元の始域の射に自然。
方針：同じ右錐の π₀ を介する二つの同値の始域自然性を合成する。
規約：両辺とも元の同じ複体射を普通の局所化へ送る。
使われ方：定値図式との導来随伴と右導来極限の普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：定値図式と実際の計算対象の導来 Hom 同値は始域に自然（Hovey §5.4）。
方針：右錐の π₀ で任意の局所化射を表示し、両側の前合成の式を使う。
規約：元の始域に cofibrancy 条件を置かず、同じ局所化像で比較する。
使われ方：導来随伴を構成する Hom 同値の始域自然性。 -/
lemma framedLimitDerivedHomEquiv_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    ∀ x : QD.obj ((Functor.const K).obj Z) ⟶ QD.obj F,
      _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y F (QD.map ((Functor.const K).map f) ≫ x) =
        Q.map f ≫ _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Z F x := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Z F).surjective x
  change _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K Y F
      ((_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Y F).symm
        (_ ≫ _root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Z F z)) = _
  rw [← _root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv_source A K f F z, Equiv.symm_apply_apply]
  simpa only [_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv_source A K f F z

end SerrePositivity.ComplexLimits
