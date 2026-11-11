module
public import SerrePositivity.KST.SConstruction.TracedCompositePartData
public import SerrePositivity.KST.SConstruction.FamilyChainBinaryPointComposition

/-! # 元の二本の単一射円柱と元の合成補正の実合成三角形
概要：元の合成補正の全 trace の二部分から、元の三円柱を三辺に持つ実三角形を構成する。
方針：元の全木の合成式と全 trace の一致を使い、同じ三角形を唯一の一点で評価する。
規約：元の全合成木・全円柱を保持し、三辺の代表を選び直さない。
使われ方：三入力の外側二面を、元の前後二本の補正と交換面へ貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全列の全 trace は、元の二つの部分の全 trace の同じ順序付き連結。 -/
lemma monicKPrismCompositeBinaryTrace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismCompositeConstantPointData F f g n).witness =
      familyChainCompositionInputTrace (monicKPrismCompositePointFirstData F f g n).witness ++
        familyChainCompositionInputTrace (monicKPrismCompositePointSecondData F f g n).witness := by
  rw [monicKPrismCompositeConstantPointData_trace, monicKPrismCompositePointFirstData_trace,
    monicKPrismCompositePointSecondData_trace]

/-- 元の二部分の全円柱と元の全合成円柱を、三辺に持つ内部 Hom の実三角形。 -/
def monicKPrismCompositeBinaryTriangle (n : ℕ) :=
  familyChainBinaryCompositionTriangle (monicKPrismCompositePointFirstData F f g n)
    (monicKPrismCompositePointSecondData F f g n) (monicKPrismCompositeConstantPointData F f g n)
    (by
      simpa only [familyChainCompositionInputTrace_eq] using
        monicKPrismCompositeBinaryTrace F f g n)

/-- 第一面全体は、元の前の単一射補正円柱の同じ後合成像。 -/
lemma monicKPrismCompositeBinaryTriangle_first (n : ℕ) :
    uncurry (stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm
      (monicKPrismCompositeBinaryTriangle F f g n).simplex) =
        (monicKPrismCompositePointFirstData F f g n).homotopy.h :=
  familyChainBinaryCompositionTriangle_first _ _ _ _

/-- 第二面全体も、元の後の単一射補正円柱の同じ BF 前合成像。 -/
lemma monicKPrismCompositeBinaryTriangle_second (n : ℕ) :
    uncurry (stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm
      (monicKPrismCompositeBinaryTriangle F f g n).simplex) =
        (monicKPrismCompositePointSecondData F f g n).homotopy.h :=
  familyChainBinaryCompositionTriangle_second _ _ _ _

/-- 対角面全体も、元の同じ合成補正円柱の一点制限そのもの。 -/
lemma monicKPrismCompositeBinaryTriangle_direct (n : ℕ) :
    uncurry (stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm
      (monicKPrismCompositeBinaryTriangle F f g n).simplex) =
        (monicKPrismCompositePointData F f g n).homotopy.h :=
  (familyChainBinaryCompositionTriangle_direct _ _ _ _).trans
    (monicKPrismCompositeConstantPointData_h F f g n)

/-- 同じ全三角形を唯一の零単体点で評価した、元の raw 写像空間の実三角形。 -/
def monicKPrismCompositeBinaryPointTriangle (n : ℕ) :=
  familyChainBinaryCompositionPointTriangle (monicKPrismCompositePointFirstData F f g n)
    (monicKPrismCompositePointSecondData F f g n) (monicKPrismCompositeConstantPointData F f g n)
    (by
      simpa only [familyChainCompositionInputTrace_eq] using
        monicKPrismCompositeBinaryTrace F f g n)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))

/-- 元の raw 空間の全二単体は、元の内部 Hom の同じ全三角形の評価像。 -/
lemma monicKPrismCompositeBinaryPointTriangle_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f g n).simplex =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryTriangle F f g n).simplex ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) :=
  familyChainBinaryCompositionPointTriangle_realization _ _ _ _ _

end SerrePositivity.KST.SConstruction
