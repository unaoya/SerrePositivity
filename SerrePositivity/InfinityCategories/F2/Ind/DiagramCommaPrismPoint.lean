module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaPrism
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointRestriction
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation

/-!
概要：元の全図式 comma の円柱の点制限を、同じ評価 comma の全余錐と同定する。
方針：内部 Hom の点評価と、標準全余錐の評価自然性を合成する。
規約：全パラメーターの変換を保つ。使われ方：始点余錐と元の円柱の境界の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全円柱を指定点で制限すると、同じ評価した元の全試験族の標準余錐になる。 -/
lemma diagramCommaPrism_point (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) (k : K _⦋0⦌) :
    (diagramShapePoint k ▷ join T (Δ[0] : SSet.{u + 1})) ≫ diagramCommaPrism κ D q =
      snd (Δ[0] : SSet.{u + 1}) (join T Δ[0]) ≫
        joinMap (q ≫ diagramCommaEvaluation κ D k) (𝟙 Δ[0]) ≫
          (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C))
            (D.app (Opposite.op ⦋0⦌) (ULift.up k))).val := by
  let L := join T (Δ[0] : SSet.{u + 1})
  let F := joinMap q (𝟙 (Δ[0] : SSet.{u + 1})) ≫ (diagramCommaCocone κ D).val
  have hm : diagramShapePoint k ▷ L = snd (Δ[0] : SSet.{u + 1}) L ≫
      lift (SSet.const (ULift.up k)) (𝟙 L) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [whiskerRight_fst, Category.assoc, lift_fst, SSet.comp_const]
      rw [diagramShapePoint, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    · simp only [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id]
  have he : F ≫ evaluateFunctorAt (ULift.up k) =
      lift (SSet.const (ULift.up k)) (𝟙 L) ≫ uncurry F := by
    simpa only [curry_uncurry] using curry_evaluateFunctorAt_vertex (uncurry F) (ULift.up k)
  change (diagramShapePoint k ▷ L) ≫ uncurry F = _
  rw [hm, Category.assoc, ← he]
  dsimp only [F]
  rw [Category.assoc, ← diagramCommaEvaluation_coconeMap κ D k]
  have hj := joinMap_comp q (diagramCommaEvaluation κ D k)
    (𝟙 (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0])
  simp only [Category.id_comp] at hj
  simpa only [Category.assoc] using congrArg (fun g => snd (Δ[0] : SSet.{u + 1}) L ≫ g ≫
    (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C))
      (D.app (Opposite.op ⦋0⦌) (ULift.up k))).val) hj.symm

end SerrePositivity.InfinityCategories.F2.Ind
