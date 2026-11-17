module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierSourceRightConeSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramSourcePiZero
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantProbeLocalization

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

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右錐の π₀ と元の定値図式の Hom の比較は始域に自然（Hovey §5.4）。
方針：同じ始域錐へ戻し、試験始域を消す自然同型の逆を前置する。
規約：元の代数と図式に cofibrancy 条件はない。
使われ方：導来随伴の Hom 比較の定値図式側の始域自然性。 -/
lemma carrierFramedLimitConePiZeroEquiv_source {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) (z : SSet.π₀ ((carrierFramedLimitConeSpace A K Z).obj F)) :
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ Complex A)).Q
    carrierFramedLimitConePiZeroEquiv A K Y F
        (SSet.mapπ₀ ((carrierFramedLimitConeSourceMap A K f).app F) z) =
      Q.map ((Functor.const K).map f) ≫ carrierFramedLimitConePiZeroEquiv A K Z F z := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ Complex A)).Q
  let P := carrierFramedLimitProbeFunctor A
  let e (X : Complex A) := carrierSourceRightConeComparisonIso A K X F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hn : (e Y).inv (SSet.mapπ₀ ((carrierFramedLimitConeSourceMap A K f).app F) z) =
      SSet.mapπ₀ ((CarrierDiagram.constantDiagramSourceMap A K (P.map f)).app
        ((Diagram.forget A K).obj F)) ((e Z).inv z) :=
    ConcreteCategory.congr_hom (carrierSourceRightConeComparisonIso_source_inv A K f F
      SSet.π₀Functor
      SimplicialModel.PiZeroLocalization.inverts_anodyne) z
  let p := carrierConstantProbeLocalizedNatIso A K
  have hp : Q.map ((Functor.const K).map f) ≫ (p.app Z).inv =
      (p.app Y).inv ≫ Q.map ((Functor.const K).map (P.map f)) := p.inv.naturality f
  change (p.app Y).inv ≫ CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (P.obj Y)
    ((Diagram.forget A K).obj F)
      ((e Y).inv (SSet.mapπ₀ ((carrierFramedLimitConeSourceMap A K f).app F) z)) ≫ 𝟙 _ =
    Q.map ((Functor.const K).map f) ≫
      ((p.app Z).inv ≫ CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (P.obj Z)
        ((Diagram.forget A K).obj F) ((e Z).inv z) ≫ 𝟙 _)
  rw [hn, CarrierDiagram.constantDiagramSourcePiZeroEquiv_source]
  simp only [Category.comp_id, ← Category.assoc]
  exact congrArg (fun g => g ≫ CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (P.obj Z)
    ((Diagram.forget A K).obj F) ((e Z).inv z))
    hp.symm

end SerrePositivity.EInfinity.BarrattEccles
