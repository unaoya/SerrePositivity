module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceShapePushout
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialHomComparison
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：始対象からの比較辺を含む合成三角形の族を、選ばれた Hom 比較と全単体で照合する。
方針：相対 coslice の充填で底の三角形を持ち上げ、始対象の評価上で二つの族をホモトピーで結ぶ。
規約：パラメータに充填性は不要。指定した底の族と可変終点を厳密に保つ。
使われ方：余錐空間の制限と部分余極限の比較辺による後合成の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 正規化した余錐の制限は、指定したパラメータの族の後合成と可換。 -/
lemma normalizedCoconeRestriction_postcomp_family {K L T X Y : SSet.{u}}
    (p : K ⟶ X) (i : L ⟶ K) (r : L ⟶ X) (hi : i ≫ p = r)
    (q : X ⟶ Y) (a : T ⟶ sliceUnder p) :
    (a ≫ normalizedCoconeRestriction p i hi) ≫ sliceUnderPostcomp r q =
      (a ≫ sliceUnderPostcomp p q) ≫
        normalizedCoconeRestriction (p ≫ q) i (by rw [← Category.assoc, hi]) := by
  apply sliceUnderUncurry_injective (r ≫ q)
  rw [sliceUnderUncurry_postcomp, normalizedCoconeRestriction_uncurry,
    normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp, Category.assoc]

/-- 指定した底の三角形の族の可変終点は、終点側の族の像と一致する。 -/
lemma relativeEdgeCosliceFamily_projection {E B T : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B)
    (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
    (b : T ⟶ sliceUnder (e ≫ q))
    (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2))) :
    b ≫ sliceUnderProjection (e ≫ q) =
      (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q := by
  rw [← sliceUnderRestrict_projection (e ≫ q) (stdSimplex.δ (0 : Fin 2)),
    ← Category.assoc, ← h]
  change (a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q) ≫
    sliceUnderProjection ((stdSimplex.δ (0 : Fin 2) ≫ e) ≫ q) = _
  rw [Category.assoc, sliceUnderPostcomp_projection, ← Category.assoc]

/-- 始対象に基づく Hom 比較は、任意の底の合成三角形の族を持ち上げて計算できる。 -/
lemma exists_initialHomEdgeFamily {E B T : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q] (c : E _⦋0⦌) (hc : IsInitialVertex c)
    (e : (Δ[1] : SSet.{u}) ⟶ E)
    (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
    (y : B _⦋0⦌) (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
    (ha : (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
    (b : T ⟶ sliceUnder (e ≫ q))
    (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2))) :
    ∃ l : T ⟶ leftFibrationInitialTotal q c y,
      l ≫ leftFibrationInitialEvaluation q c y =
        vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha ∧
      l ≫ leftFibrationInitialProjection q c y ≫
          vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
        b ≫ normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
          (by rw [← Category.assoc, he]) ∧
      Nonempty (SSet.Homotopy
        ((vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha) ≫
          leftFibrationInitialSection q c hc y) l) := by
  obtain ⟨L, hL, hq⟩ := exists_relativeEdgeCosliceLift e q a b h
  let s := L ≫ normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he
  have hs : s ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c) =
      a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) := by
    dsimp only [s]
    rw [Category.assoc, normalizedCoconeRestriction_projection,
      ← sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2)), ← Category.assoc, hL]
  have hsy : s ≫ (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) = SSet.const y := by
    rw [← Category.assoc, hs, ha]
  let l := vertexFiberLift (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y s hsy
  have hl : l ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y = s :=
    vertexFiberLift_ι _ _ _ _
  have hev : l ≫ leftFibrationInitialEvaluation q c y =
      vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha := by
    apply vertexFiber_hom_ext q y
    rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
      ← Category.assoc, hl, vertexFiberLift_ι, hs]
  have hp : l ≫ leftFibrationInitialProjection q c y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      b ≫ normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
        (by rw [← Category.assoc, he]) := by
    rw [leftFibrationInitialProjection, vertexFiberMap_ι, ← Category.assoc, hl]
    change (L ≫ normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he) ≫
      sliceUnderPostcomp (SSet.yonedaEquiv.symm c) q = _
    rw [normalizedCoconeRestriction_postcomp_family, hq]
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  obtain ⟨H, _⟩ := exists_homotopy_over_trivialKanFibration
    (leftFibrationInitialEvaluation q c y)
    ((vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha) ≫
      leftFibrationInitialSection q c hc y) l
    (by rw [Category.assoc, leftFibrationInitialSection_evaluation, Category.comp_id, hev])
  exact ⟨l, hev, hp, ⟨H⟩⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
