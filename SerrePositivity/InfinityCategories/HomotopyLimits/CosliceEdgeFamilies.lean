module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：固定した辺に沿う coslice の前合成を全パラメータで作り、底を指定して持ち上げる。
方針：終点への制限と相対終点制限の自明 Kan fibration 性から切断を選ぶ。
規約：前合成の選択には厳密な終点評価を持たせる。相対持ち上げでは底の余錐全体を固定する。
使われ方：部分余極限の Hom 比較と、比較辺による後合成の高次の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 固定辺の終点側の余錐を、辺全体の余錐へ延長する切断。 -/
def cosliceEdgeSection {X : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X) :
    sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e) ⟶ sliceUnder e := by
  have := sliceUnderRestrict_target_trivialKanFibration e
  exact (trivialKanFibration_exists_section
    (sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)))).choose

/-- 選んだ辺の延長の終点側は、元の余錐の族を厳密に再現する。 -/
lemma cosliceEdgeSection_target {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    cosliceEdgeSection e ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = 𝟙 _ := by
  have := sliceUnderRestrict_target_trivialKanFibration e
  exact (trivialKanFibration_exists_section
    (sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)))).choose_spec

/-- 固定した実際の辺に沿う、coslice 全体の前合成。 -/
def cosliceEdgePrecomposition {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e) ⟶
      sliceUnder (stdSimplex.δ (1 : Fin 2) ≫ e) :=
  cosliceEdgeSection e ≫ sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2))

/-- 辺による前合成は、余錐の可変な終点の全単体を保つ。 -/
lemma cosliceEdgePrecomposition_projection {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    cosliceEdgePrecomposition e ≫ sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ e) =
      sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  rw [cosliceEdgePrecomposition, Category.assoc, sliceUnderRestrict_projection,
    ← sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2)),
    ← Category.assoc, cosliceEdgeSection_target, Category.id_comp]

/-- inner fibration の固定辺から終点への相対 coslice 制限も自明 Kan fibration。 -/
lemma relativeCosliceRestriction_target_trivialKanFibration {E B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    TrivialKanFibration (relativeCosliceRestriction e q (stdSimplex.δ (0 : Fin 2))) := by
  let A : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face {(0 : Fin 2)}ᶜ
  have hA : rightAnodyneExtensions A.ι := by
    rw [← rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom,
      stdSimplex.faceSingletonComplIso_hom_ι]
    exact endpointInclusion_rightAnodyne
  have := relativeCosliceMap_trivialKanFibration_of_rightAnodyne e q A hA
  have h := relativeCosliceRestriction_trivialKanFibration_subcomplexIso e q A
    (stdSimplex.faceSingletonComplIso (0 : Fin 2))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 指定した底の合成三角形の族を、終点側の族を保って全空間へ持ち上げる。 -/
lemma exists_relativeEdgeCosliceLift {E B T : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
    (b : T ⟶ sliceUnder (e ≫ q))
    (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2))) :
    ∃ l : T ⟶ sliceUnder e,
      l ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = a ∧
        l ≫ sliceUnderPostcomp e q = b := by
  have := relativeCosliceRestriction_target_trivialKanFibration e q
  let v := pullback.lift a b h
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section
    (relativeCosliceRestriction e q (stdSimplex.δ (0 : Fin 2)))
  refine ⟨v ≫ s, ?_, ?_⟩
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.fst _ _) hs
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using ht
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.snd _ _) hs
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using ht

end
end SerrePositivity.InfinityCategories.HomotopyLimits
