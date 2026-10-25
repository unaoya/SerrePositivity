module

public import SerrePositivity.InfinityCategories.F2.Ind.PosetLowerRestrictionCofinality
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTargetEvaluationCofinality

/-!
概要：元の有限半順序全図式の任意の指定点で、実表示 comma の評価は right cofinal。
方針：指定点の弱下方部分へ制限し、元の厳密下方余錐の極大点評価を接続する。
規約：元の全評価写像と元の指定点を保持する。
使われ方：有限半順序形状の同じ標準全余錐の余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の有限半順序図式の各指定点評価自身は right cofinal。
方針：弱下方制限と余錐極大点評価を合成する。
規約：元の全評価。使われ方：同じ全図式の単一 filtered 表示。 -/
lemma diagramCommaEvaluation_finitePoset_isRightCofinal (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {P : Type u} [PartialOrder P] [Finite P] {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)
    (k : (nerve P) _⦋0⦌) : IsRightCofinal (diagramCommaEvaluation κ D k) := by
  let p := nerveEquiv k
  let U : Set P := Set.Iic p
  let r := nerveMap (OrderHom.Subtype.val U).toFunctor
  let L := nerve {x : P // x < p}
  let s := (F1B.posetLowerJoinIso p).hom
  let D₁ := (SSet.uliftFunctor.{u + 1, u}).map r ≫ D
  let D₂ := (SSet.uliftFunctor.{u + 1, u}).map s ≫ D₁
  have hR₁ : IsRightCofinal (diagramCommaRestriction κ D r) :=
    diagramCommaRestriction_poset_lowerSet_isRightCofinal κ U
      (by intro x y hxy hy; exact le_trans hxy hy) D
  letI := diagramCommaRestriction_isIso κ D₁ s
  have hR₂ := isRightCofinal_of_isIso (diagramCommaRestriction κ D₁ s)
  have hLower : IsKappaFiltered κ (smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D₂)) :=
    smallFinitePosetDiagramComma_isKappaFiltered κ _
  have hE := diagramCommaEvaluation_cone_apex_isRightCofinal κ D₂
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le L) hLower
  have h := hR₁.comp (hR₂.comp hE)
  change IsRightCofinal (diagramCommaRestriction κ D r ≫
    diagramCommaRestriction κ D₁ s ≫ diagramCommaEvaluation κ D₂ (coneApex L)) at h
  rw [diagramCommaRestriction_evaluate, diagramCommaRestriction_evaluate] at h
  have hk : r.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) (coneApex L)) = k := by
    have hpoint := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ nerve {x : P // x ≤ p} ↦
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) (F1B.posetLowerJoinIso_inr p)
    change s.app (Opposite.op ⦋0⦌) (coneApex L) = _ at hpoint
    rw [hpoint]
    apply nerveEquiv.injective
    rfl
  exact Eq.mp (congrArg (fun v ↦ IsRightCofinal (diagramCommaEvaluation κ D v)) hk) h

end SerrePositivity.InfinityCategories.F2.Ind
