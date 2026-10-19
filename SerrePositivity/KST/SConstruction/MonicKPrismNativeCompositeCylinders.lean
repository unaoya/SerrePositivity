module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCorrectionChains
public import SerrePositivity.KST.SConstruction.FamilyChainCompositionSquares

/-! # 元の全補正列から構成する K の実比較円柱
概要：共通三精密化上の有限補正列を、元の全区間と合成三角形を保つ一本の円柱にする。
方針：保存済みの実補正列へ Kan 標的の合成構成を適用する。
規約：零段では円柱全体を定数とし、全段で元の trace を省略しない。
使われ方：実 raw 比較の構造適合を構成する際の、各段の比較円柱。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open Spectra.PointedMapping
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の合成射から BF 合成の raw 評価までの実円柱と元の全合成証人。 -/
def monicKPrismNativeCompositeCorrectionData (n : ℕ) :=
  familyChainCompositeData (monicKPrismNativeCompositeCorrectionChain F f g n)

/-- 一本の実円柱の合成証人から、元の全補正区間を同じ順序で回収する。 -/
lemma monicKPrismNativeCompositeCorrectionData_trace (n : ℕ) :
    familyChainCompositionInputTrace
        (monicKPrismNativeCompositeCorrectionData F f g n).witness =
      (familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g n)).map
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [familyChainCompositionInputTrace_eq, monicKPrismNativeCompositeCorrectionChain_trace]

/-- 零段では比較円柱の全時刻が同じ元の合成射に固定される。 -/
lemma monicKPrismNativeCompositeCorrectionData_zero :
    (monicKPrismNativeCompositeCorrectionData F f g 0).homotopy.h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  familyChainCompositeData_constant_of_trace_nil _
    (monicKPrismNativeCompositeCorrectionChain_zero_trace F f g)

/-- 全第二面から補正済みの後続適合円柱への実二次元円柱と全三角形。 -/
def monicKPrismNativeSecondCompatibilityData (n : ℕ) :=
  familyChainCompositeData (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 二次元比較も元の全交換正方形を保持し、途中の区間を省略しない。 -/
lemma monicKPrismNativeSecondCompatibilityData_trace (n : ℕ) :
    familyChainCompositionInputTrace
        (monicKPrismNativeSecondCompatibilityData F f g n).witness =
      (familyHomotopyChainTrace (monicKPrismCompositeSecondCompatibilityTransport F f g n)).map
        (((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [familyChainCompositionInputTrace_eq, monicKPrismNativeSecondCompatibilityTransport_trace]

/-- 零段の二次元比較は元の第二面の全時刻での定数円柱。 -/
lemma monicKPrismNativeSecondCompatibilityData_zero :
    (monicKPrismNativeSecondCompatibilityData F f g 0).homotopy.h =
      fst (nerve (CompositionStringParameters f g) ⊗ (Δ[1] : SSet.{u}))
        (Δ[1] : SSet.{u}) ≫
      (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismCompositionNativeTriangle 0 F f g := by
  exact familyChainCompositeData_constant_of_trace_nil _
    (monicKPrismNativeSecondCompatibilityTransport_zero_trace F f g)

end SerrePositivity.KST.SConstruction
