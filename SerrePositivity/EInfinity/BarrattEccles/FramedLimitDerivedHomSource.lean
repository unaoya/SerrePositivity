module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitConePiZeroSource
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitHomSource

/-!
# 定値図式と具体的な極限計算対象の導来 Hom 同値の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の導来 Hom の同値は元の始域の射に自然。
方針：同じ右錐の π₀ を介する二つの同値の始域自然性を合成する。
規約：両辺とも元の同じ代数射を普通の局所化へ送る。
使われ方：定値図式との導来随伴と右導来極限の普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：定値図式と実際の計算対象の導来 Hom 同値は始域に自然（Hovey §5.4）。
方針：右錐の π₀ で任意の局所化射を表示し、両側の前合成の式を使う。
規約：元の始域に cofibrancy 条件を置かず、同じ局所化像で比較する。
使われ方：導来随伴を構成する Hom 同値の始域自然性。 -/
lemma framedLimitDerivedHomEquiv_source {Y Z : (operad A).Algebra} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    ∀ x : QD.obj ((Functor.const K).obj Z) ⟶ QD.obj F,
      framedLimitDerivedHomEquiv A K Y F (QD.map ((Functor.const K).map f) ≫ x) =
        Q.map f ≫ framedLimitDerivedHomEquiv A K Z F x := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (framedLimitConePiZeroEquiv A K Z F).surjective x
  change framedLimitHomPiZeroEquiv A K Y F
      ((framedLimitConePiZeroEquiv A K Y F).symm
        (_ ≫ framedLimitConePiZeroEquiv A K Z F z)) = _
  rw [← framedLimitConePiZeroEquiv_source A K f F z, Equiv.symm_apply_apply]
  simpa only [framedLimitDerivedHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    framedLimitHomPiZeroEquiv_source A K f F z

end SerrePositivity.EInfinity.BarrattEccles
