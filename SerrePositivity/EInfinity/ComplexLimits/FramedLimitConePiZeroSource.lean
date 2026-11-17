module

public import SerrePositivity.EInfinity.ComplexLimits.SourceRightConeSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramSourcePiZero
public import SerrePositivity.EInfinity.ComplexLimits.ConstantProbeLocalization

/-!
# 右錐の π₀ と定値図式の局所化 Hom 比較の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の右錐の π₀ 比較は元の始域の射に自然。
方針：両錐比較の逆の自然性と二つの置換比較の自然性を合成する。
規約：前合成は元の射の定値図式の同じ局所化像。
使われ方：定値図式と具体的な計算対象の導来 Hom 同値。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右錐の π₀ と元の定値図式の Hom の比較は始域に自然（Hovey §5.4）。
方針：同じ始域錐へ戻し、試験始域を消す自然同型の逆を前置する。
規約：元の複体と図式に cofibrancy 条件はない。
使われ方：導来随伴の Hom 比較の定値図式側の始域自然性。 -/
lemma framedLimitConePiZeroEquiv_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) (z : SSet.π₀ ((framedLimitConeSpace A K Z).obj F)) :
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    framedLimitConePiZeroEquiv A K Y F
        (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z) =
      Q.map ((Functor.const K).map f) ≫ framedLimitConePiZeroEquiv A K Z F z := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  let P := framedLimitProbeFunctor A
  let e (X : (Complex A)) := sourceRightConeComparisonIso A K X F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hn : (e Y).inv (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z) =
      SSet.mapπ₀ ((BarrattEccles.CarrierDiagram.constantDiagramSourceMap A K (P.map f)).app F) ((e
        Z).inv z) :=
    ConcreteCategory.congr_hom (sourceRightConeComparisonIso_source_inv A K f F SSet.π₀Functor
      SimplicialModel.PiZeroLocalization.inverts_anodyne) z
  let p := constantProbeLocalizedNatIso A K
  have hp : Q.map ((Functor.const K).map f) ≫ (p.app Z).inv =
      (p.app Y).inv ≫ Q.map ((Functor.const K).map (P.map f)) := p.inv.naturality f
  change (p.app Y).inv ≫ BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (P.obj
    Y) F
      ((e Y).inv (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z)) ≫ 𝟙 _ =
    Q.map ((Functor.const K).map f) ≫
      ((p.app Z).inv ≫ BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (P.obj Z)
        F ((e Z).inv z) ≫ 𝟙 _)
  rw [hn, BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_source]
  simp only [Category.comp_id, ← Category.assoc]
  exact congrArg (fun g => g ≫ BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K
    (P.obj Z) F ((e Z).inv z))
    hp.symm

end SerrePositivity.EInfinity.ComplexLimits
