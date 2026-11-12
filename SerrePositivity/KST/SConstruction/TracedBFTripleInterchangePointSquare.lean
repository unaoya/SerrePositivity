module
public import SerrePositivity.KST.SConstruction.TracedBFTripleInterchangeDiamond

/-! # 元の全交換族と実辺の正方形の厳密な照合
概要：最終射の直通列点で、元の全二時刻交換族を同じ二実辺の正方形へ照合する。
方針：同じ単一射補正の全区間回収と、元の BF 段辺の全円柱を使う。
規約：一点での端点だけでなく全二時刻の実写像を厳密に同定する。
使われ方：元の全交換族から、実三角形対に用いる同じ二辺への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の全補正辺と元の BF 段辺を独立な二時刻で合成した実正方形。 -/
def monicKTracedTripleInterchangePointSquare (n : ℕ) :=
  lift (fst (Δ[1] : SSet.{u}) Δ[1] ≫
      SSet.yonedaEquiv.symm (monicKTracedUnaryCorrectionPointEdge F h n).edge)
    (snd (Δ[1] : SSet.{u}) Δ[1] ≫
      SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge) ≫
        kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n

/-- 元の全交換族の直通列点制限は、実三角形対に用いた同じ二辺の全正方形そのもの。 -/
lemma monicKTracedTripleInterchangeFamily_point (n : ℕ) :
    (pointParameterMap (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect h)))
        (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
          monicKTracedTripleInterchangeFamily F f g h n =
      monicKTracedTripleInterchangePointSquare F f g h n := by
  rw [monicKTracedTripleInterchangeFamily, monicKTracedTripleBFInterchangeCylinder,
    pointedCorrectionInterchange_point]
  unfold monicKTracedTripleInterchangePointSquare
  rw [monicKTracedUnaryCorrectionPointEdge_map]
  rfl

end SerrePositivity.KST.SConstruction
