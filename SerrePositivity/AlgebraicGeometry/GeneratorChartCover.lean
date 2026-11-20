module

public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：KST §5、Stacks 080Y の中心の生成族による blowup の標準チャート被覆。
方針：生成族の次数一元を含む斉次素イデアルが次数一成分全体を含むことを示す。
規約：生成族は有限に限らず、有限生成の場合に有限被覆を取り出す。
使われ方：有限チャート族で構成した降下中心を blowup 全体で評価する。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open Polynomial _root_.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} (C : ι → I)

/--
概要：中心の生成族の Rees 次数一元を含むイデアルは次数一成分全体を含む。
方針：単項式の逆像部分加群で基礎環のイデアル生成性を使う。
規約：KST §5、Stacks 080Y、素性を要求しない。
使われ方：生成族による標準チャート被覆の環論的入力。
-/
theorem contains_degreeOne_of_contains_generators
    (hC : Ideal.span (Set.range (fun i => (C i).1)) = I)
    (P : Ideal (reesAlgebra I)) (hP : ∀ i, reesDegreeOne I (C i) ∈ P) :
    ∀ a : I, reesDegreeOne I a ∈ P := by
  let T : Submodule R R :=
    ((P.restrictScalars R).map (reesAlgebra I).val.toLinearMap).comap (monomial 1)
  have hspan : I ≤ T := by
    rw [← hC]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨reesDegreeOne I (C i), hP i, rfl⟩
  intro a
  obtain ⟨p, hp, heq⟩ := hspan a.2
  have heq' : p = reesDegreeOne I a := Subtype.ext heq
  rwa [← heq']

/--
概要：中心の任意の生成族に対応する標準チャートは blowup 全体を覆う。
方針：被覆の外の斉次素イデアルが次数一元を全て含む矛盾を得る。
規約：KST §5、Stacks 080Y、有限生成性なしに成立する。
使われ方：有限生成族を選んだときの有限チャート被覆。
-/
theorem iSup_affineBlowup_generatorCharts
    (hC : Ideal.span (Set.range (fun i => (C i).1)) = I) :
    ⨆ i, affineBlowupChart I (C i) = ⊤ := by
  classical
  apply top_unique
  intro x _
  by_contra hnot
  have hP (i : ι) : reesDegreeOne I (C i) ∈ x.asHomogeneousIdeal.toIdeal := by
    by_contra hi
    exact hnot (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
  have hall := contains_degreeOne_of_contains_generators I C hC x.asHomogeneousIdeal.toIdeal hP
  have htop : x ∈ (⊤ : (affineBlowup I).Opens) := trivial
  rw [← iSup_affineBlowupChart I] at htop
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  exact ha (hall a)

/--
概要：中心の生成族に対応する実際のアフィン開被覆。
方針：生成族チャートの被覆性から点ごとの添字を選ぶ。
規約：KST §5、Stacks 080Y、添字族の有限性を保持する。
使われ方：有限生成な中心でのイデアル降下の幾何学的被覆。
-/
def affineBlowupGeneratorChartCover
    (hC : Ideal.span (Set.range (fun i => (C i).1)) = I) :
    (affineBlowup I).AffineOpenCover where
  I₀ := ι
  X i := CommRingCat.of (BlowupChartRing I (C i))
  f i := affineBlowupChartι I (C i)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineBlowup_generatorCharts I C hC).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι I _).opensRange
    rw [show (affineBlowupChartι I _).opensRange = affineBlowupChart I _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineBlowup_generatorCharts I C hC).ge (Set.mem_univ x))).choose_spec

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
