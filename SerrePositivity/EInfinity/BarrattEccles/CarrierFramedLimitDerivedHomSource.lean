module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitConePiZeroSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitHomSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitHomNaturality

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

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：定値図式と実際の計算対象の導来 Hom 同値は始域に自然（Hovey §5.4）。
方針：右錐の π₀ で任意の局所化射を表示し、両側の前合成の式を使う。
規約：元の始域に cofibrancy 条件を置かず、同じ局所化像で比較する。
使われ方：導来随伴を構成する Hom 同値の始域自然性。 -/
lemma carrierFramedLimitDerivedHomEquiv_source {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    ∀ x : QD.obj ((Functor.const K).obj Z) ⟶ QD.obj ((Diagram.forget A K).obj F),
      carrierFramedLimitDerivedHomEquiv A K Y F (QD.map ((Functor.const K).map f) ≫ x) =
        Q.map f ≫ carrierFramedLimitDerivedHomEquiv A K Z F x := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (carrierFramedLimitConePiZeroEquiv A K Z F).surjective x
  change carrierFramedLimitHomPiZeroEquiv A K F Y
      ((carrierFramedLimitConePiZeroEquiv A K Y F).symm
        (_ ≫ carrierFramedLimitConePiZeroEquiv A K Z F z)) = _
  rw [← carrierFramedLimitConePiZeroEquiv_source A K f F z, Equiv.symm_apply_apply]
  simpa only [carrierFramedLimitDerivedHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    carrierFramedLimitHomPiZeroEquiv_source A K f F z

/-- 概要：底の導来 Hom 同値は両変数の同じ局所化射に自然（Hovey §5.4）。
方針：元の複体射の前合成と元の図式射の後合成の二つの自然性を合成する。
規約：元の複体にも代数図式にも cofibrancy 条件はない。
使われ方：底の導来 Hom 同値を二変数の自然同型へ束ねる。 -/
lemma carrierFramedLimitDerivedHomEquiv_both {Y Z : Complex A} (f : Y ⟶ Z)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    ∀ x : QD.obj ((Functor.const K).obj Z) ⟶ QD.obj ((Diagram.forget A K).obj F),
      carrierFramedLimitDerivedHomEquiv A K Y G
        (QD.map ((Functor.const K).map f) ≫ x ≫ QD.map ((Diagram.forget A K).map g)) =
      Q.map f ≫ carrierFramedLimitDerivedHomEquiv A K Z F x ≫
        Q.map ((framedLimitFunctor A K).map g).hom := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (Complex A)).Q
  let QD := (weakEquivalences (K ⥤ Complex A)).Q
  dsimp only
  intro x
  have hs := carrierFramedLimitDerivedHomEquiv_source A K f G
    (x ≫ QD.map ((Diagram.forget A K).map g))
  have ht := carrierFramedLimitDerivedHomEquiv_target A K Z g x
  exact hs.trans (congrArg (fun z => Q.map f ≫ z) ht)

end SerrePositivity.EInfinity.BarrattEccles
