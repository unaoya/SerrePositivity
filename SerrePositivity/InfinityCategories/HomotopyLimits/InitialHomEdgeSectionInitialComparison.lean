module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeSectionComparison

/-!
概要：保持した同じ全辺族の終点・底固定比較を、元の中間持ち上げへの初期 Hom 円柱へ移す。
方針：比較円柱を同じ初期頂点へ制限し、固定終点の fiber に戻す。
規約：終点は既存データの lift そのもの。使われ方：前置写像と元の HL・HR の類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (hc : IsInitialVertex c) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c) (y : B _⦋0⦌)
  (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ sliceUnder (e ≫ q))
  (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)))
  (hb : b = a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫
    cosliceEdgeSection (e ≫ q))
local notation "D" => initialHomEdgeCylinder q c hc e he y a ha b h
local notation "H" => initialHomEdgeSectionComparison q c hc e he y a ha b h hb
local notation "P" => normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he
local notation "v" => vertexFiberLift q y
  (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha

include ha in
/-- 普遍相対切断の像も、同じ底の終点 y 上に留まる。 -/
lemma initialHomEdgeSectionInput_fixed :
    ((a ≫ relativeEdgeCosliceSection e q) ≫ sliceUnderProjection e) ≫ q = SSet.const y := by
  rw [Category.assoc a (relativeEdgeCosliceSection e q) (sliceUnderProjection e),
    relativeEdgeCosliceSection_projection]
  exact ha

/-- 同じ全辺族の比較中も、底の終点は円柱の全時刻で y に固定される。 -/
lemma initialHomEdgeSectionComparison_fixed :
    ((H).h ≫ sliceUnderProjection e) ≫ q = SSet.const y := by
  calc
    _ = ((H).h ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2))) ≫
        (sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) ≫ q) := by
      simpa only [Category.assoc] using
        (congrArg (fun z ↦ ((H).h ≫ z) ≫ q)
          (sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2))).symm)
    _ = (fst T Δ[1] ≫ a) ≫
        (sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) ≫ q) :=
      congrArg (· ≫ _) (initialHomEdgeSectionComparison_target q c hc e he y a ha b h hb)
    _ = fst T Δ[1] ≫ ((a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q) := by
      simp only [Category.assoc]
    _ = _ := by rw [ha, SSet.comp_const]

/-- 全辺族の同じ比較を初期 Hom に制限し、元の lift を終点として保持する。 -/
def initialHomEdgeSectionInitialComparison : SSet.Homotopy
    (initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y
      (a ≫ relativeEdgeCosliceSection e q)
      (initialHomEdgeSectionInput_fixed q e y a ha)) (InitialHomEdgeCylinder.lift D) where
  h := vertexFiberLift (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y ((H).h ≫ P)
    (by
      rw [← Category.assoc ((H).h ≫ P), Category.assoc (H).h P,
        normalizedCoconeRestriction_projection]
      exact initialHomEdgeSectionComparison_fixed q c hc e he y a ha b h hb)
  h₀ := by
    change SSet.ι₀ ≫ vertexFiberLift _ y ((H).h ≫ P) _ =
      initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y
        (a ≫ relativeEdgeCosliceSection e q) (initialHomEdgeSectionInput_fixed q e y a ha)
    apply vertexFiber_hom_ext
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, SSet.Homotopy.h₀,
      initialDiagramHomFamily, vertexFiberLift_ι]
  h₁ := by
    change SSet.ι₁ ≫ vertexFiberLift _ y ((H).h ≫ P) _ = (D).lift
    apply vertexFiber_hom_ext
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, SSet.Homotopy.h₁]
    exact (D).lift_ι.symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
local notation "K" => initialHomEdgeSectionInitialComparison q c hc e he y a ha b h hb

/-- 包含後は、元の同じ全辺族の比較円柱の初期制限そのもの。 -/
lemma initialHomEdgeSectionInitialComparison_ι :
    (K).h ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y = (H).h ≫ P := by
  rw [initialHomEdgeSectionInitialComparison, vertexFiberLift_ι]

/-- 初期 Hom 比較の評価は、元の終点側の全族を全時刻で厳密に保持する。 -/
lemma initialHomEdgeSectionInitialComparison_evaluation :
    (K).h ≫ leftFibrationInitialEvaluation q c y = fst T Δ[1] ≫ v := by
  apply vertexFiber_hom_ext q y
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι, ← Category.assoc,
    initialHomEdgeSectionInitialComparison_ι, Category.assoc,
    normalizedCoconeRestriction_projection, Category.assoc, vertexFiberLift_ι]
  have hH := congrArg (· ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e))
    (initialHomEdgeSectionComparison_target q c hc e he y a ha b h hb)
  simpa only [Category.assoc, sliceUnderRestrict_projection] using hH

/-- 初期 Hom 比較の底も、元の lift の底の全族を全時刻で固定する。 -/
lemma initialHomEdgeSectionInitialComparison_base :
    (K).h ≫ leftFibrationInitialProjection q c y =
      fst T Δ[1] ≫ (D).lift ≫ leftFibrationInitialProjection q c y := by
  let R := normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) he))
  have hp : (K).h ≫ leftFibrationInitialProjection q c y ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      ((H).h ≫ sliceUnderPostcomp e q) ≫ R := by
    rw [leftFibrationInitialProjection, vertexFiberMap_ι,
      ← Category.assoc, initialHomEdgeSectionInitialComparison_ι]
    exact normalizedCoconeRestriction_postcomp_family e (stdSimplex.δ (1 : Fin 2))
      (SSet.yonedaEquiv.symm c) he q (H).h
  have hd : (D).lift ≫ leftFibrationInitialProjection q c y ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y = b ≫ R := by
    rw [← Category.assoc (D).lift (leftFibrationInitialProjection q c y)
      (vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y),
      (D).projection, initialEdgeBaseSource, vertexFiberLift_ι]
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  exact (Category.assoc _ _ _).trans
    (hp.trans ((congrArg (· ≫ R)
      (initialHomEdgeSectionComparison_base q c hc e he y a ha b h hb)).trans
        ((Category.assoc _ _ _).trans ((congrArg (fst T Δ[1] ≫ ·) hd.symm).trans
          (Category.assoc _ _ _).symm))))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
