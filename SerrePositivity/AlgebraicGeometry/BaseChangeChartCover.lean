module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartBaseChange
public import SerrePositivity.AlgebraicGeometry.Exceptional

/-!
概要：KST §5 の像中心の blowup の、元の中心元による標準チャート被覆。
方針：像イデアルの線形生成性を次数一の単項式へ移す。
規約：係数環準同型は任意であり、全射性・平坦性は仮定しない。
使われ方：局所化後の blowup 全体を元の中心のチャートで比較する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Polynomial
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)

/--
概要：像中心の全ての元の次数一単項式は、元の中心元の像からイデアルとして生成される。
方針：単項式写像の逆像の部分加群で像イデアルの生成性を使う。
規約：KST §5、任意の Rees 代数のイデアルに対する所属判定。
使われ方：元の中心元に対応するチャートの被覆性。
-/
theorem contains_degreeOne_of_contains_image (P : Ideal (reesAlgebra (I.map f)))
    (hP : ∀ a : I, reesDegreeOne (I.map f) (centerImageElement I _ f le_rfl a) ∈ P) :
    ∀ b : I.map f, reesDegreeOne (I.map f) b ∈ P := by
  let T : Submodule S S :=
    ((P.restrictScalars S).map (reesAlgebra (I.map f)).val.toLinearMap).comap (monomial 1)
  have hspan : I.map f ≤ T := by
    change Submodule.span S (f '' (I : Set R)) ≤ T
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨reesDegreeOne (I.map f) (centerImageElement I _ f le_rfl ⟨r, hr⟩),
      hP ⟨r, hr⟩, ?_⟩
    rfl
  intro b
  obtain ⟨p, hp, heq⟩ := hspan b.2
  have hpb : p = reesDegreeOne (I.map f) b := Subtype.ext heq
  exact hpb ▸ hp

/--
概要：元の中心元の像に対応する標準チャートは像中心の blowup 全体を覆う。
方針：覆われない点の素イデアルに全ての次数一元が入る矛盾を導く。
規約：KST §5、有限生成性は不要。
使われ方：局所化後のチャート同型を大域化するための被覆。
-/
theorem iSup_affineBlowup_imageCharts :
    (⨆ a : I, affineBlowupChart (I.map f) (centerImageElement I _ f le_rfl a)) = ⊤ := by
  apply top_unique
  intro x _
  by_contra hnot
  have hP (a : I) : reesDegreeOne (I.map f) (centerImageElement I _ f le_rfl a) ∈
      x.asHomogeneousIdeal.toIdeal := by
    by_contra ha
    exact hnot (TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩)
  have hall := contains_degreeOne_of_contains_image I f x.asHomogeneousIdeal.toIdeal hP
  have htop : x ∈ (⊤ : (affineBlowup (I.map f)).Opens) := trivial
  rw [← iSup_affineBlowupChart (I.map f)] at htop
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  exact hb (hall b)

/--
概要：元の中心の元を添字とする、像中心の blowup の実際のアフィン開被覆。
方針：像元に対応する標準チャートの被覆性から各点の添字を選ぶ。
規約：KST §5、被覆のチャートは斉次局所化環の Spec。
使われ方：開基底変更の比較射の局所同型を全体へ移す。
-/
def affineBlowupImageChartCover : (affineBlowup (I.map f)).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (BlowupChartRing (I.map f) (centerImageElement I _ f le_rfl a))
  f a := affineBlowupChartι (I.map f) (centerImageElement I _ f le_rfl a)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineBlowup_imageCharts I f).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι (I.map f) _).opensRange
    rw [show (affineBlowupChartι (I.map f) _).opensRange = affineBlowupChart (I.map f) _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineBlowup_imageCharts I f).ge (Set.mem_univ x))).choose_spec

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
