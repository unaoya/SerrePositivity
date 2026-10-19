module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeComparison

/-!
概要：比較辺の合成三角形を通す Hom 比較を、評価固定の実際の中間円柱として保持する。
方針：元の相対持ち上げの評価・底への像を保持し、自明 Kan 評価上で円柱を選ぶ。
規約：裸のホモトピー存在命題からは選ばない。円柱の全時刻で同じ終点の族を評価する。
使われ方：余錐制限の正方形の比較と共通 end における高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}}
  (q : E ⟶ B) (c : E _⦋0⦌) (hc : IsInitialVertex c) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ sliceUnder (e ≫ q))
  (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)))
local notation "v" => vertexFiberLift q y
  (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha

/-- 中間の実際の持ち上げと、その評価を固定する同じ Hom 比較円柱。 -/
structure InitialHomEdgeCylinder where
  lift : T ⟶ leftFibrationInitialTotal q c y
  evaluation : lift ≫ leftFibrationInitialEvaluation q c y = v
  projection : lift ≫ leftFibrationInitialProjection q c y =
    initialEdgeBaseSource q c e he y a ha b h
  homotopy : SSet.Homotopy (v ≫ leftFibrationInitialSection q c hc y) lift
  fixedEvaluation : homotopy.h ≫ leftFibrationInitialEvaluation q c y =
    fst T (Δ[1] : SSet.{u}) ≫ v

/-- 元の合成三角形の評価と底の族を保つ、評価固定の比較データを構成する。 -/
def initialHomEdgeCylinder [InnerFibration q] : InitialHomEdgeCylinder q c hc e he y a ha b h :=
  Classical.choice (by
    obtain ⟨l, hev, hp, _⟩ := exists_initialHomEdgeFamily q c hc e he y a ha b h
    have hl : l ≫ leftFibrationInitialProjection q c y =
        initialEdgeBaseSource q c e he y a ha b h := by
      apply vertexFiber_hom_ext
      rw [Category.assoc]
      exact hp
    have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
    obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration
      (leftFibrationInitialEvaluation q c y) (v ≫ leftFibrationInitialSection q c hc y) l
      (by rw [Category.assoc, leftFibrationInitialSection_evaluation, Category.comp_id, hev])
    exact ⟨⟨l, hev, hl, H, by simpa only [Category.assoc, hev] using hH⟩⟩)

variable [InnerFibration q]

/-- 左 pinched Hom の比較は、同じ評価固定円柱の射影そのものとして構成する。 -/
def initialHomEdgePinchedCylinder : SSet.Homotopy
    (v ≫ leftFibrationInitialHomComparison q c hc y)
    (initialEdgeBaseSource q c e he y a ha b h ≫ (leftFibrationInitialBaseIso q c y).hom) := by
  let D := initialHomEdgeCylinder q c hc e he y a ha b h
  let H := functorHomotopyPostcomp D.homotopy
    (leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom)
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = v ≫ leftFibrationInitialHomComparison q c hc y
        simpa only [leftFibrationInitialHomComparison, Category.assoc] using H.h₀
      h₁ := by
        change SSet.ι₁ ≫ H.h =
          initialEdgeBaseSource q c e he y a ha b h ≫ (leftFibrationInitialBaseIso q c y).hom
        exact H.h₁.trans (by rw [← Category.assoc, D.projection])
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- Hom 比較の raw な円柱は、中間円柱の同じ射影である。 -/
lemma initialHomEdgePinchedCylinder_projection :
    (initialHomEdgePinchedCylinder q c hc e he y a ha b h).h =
      (initialHomEdgeCylinder q c hc e he y a ha b h).homotopy.h ≫
        leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom := rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
