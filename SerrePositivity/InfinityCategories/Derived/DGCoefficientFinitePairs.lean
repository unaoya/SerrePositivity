module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalInduction
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientRelativeFiller
public import SerrePositivity.InfinityCategories.Derived.SkeletalFiniteBound

/-! # 一般有限対の閉分母後の係数充填

概要：有限単体集合の指定部分と商図式の任意の厳密正方形を、一つの閉分母後に充填する。
方針：相対骨格の状態を有限次数まで帰納し、標的全体との同型で係数充填を取り出す。
規約：指定部分の厳密制限と比較の全時刻固定を保つ。使われ方：実屋根比較の有限対検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (x y : D)
variable (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 全体に達した骨格状態から、同じ閉分母と境界固定比較の相対充填を取り出す。 -/
def DGCoefficientSkeletalStage.toRelativeFiller {n : ℕ}
    (S : DGCoefficientSkeletalStage A D P i n x y a g)
    (hn : skeletonOfMono i n = ⊤) : DGCoefficientRelativeFiller A D P i x y a g := by
  let e : (skeletonOfMono i n : SSet) ≅ K :=
    Subcomplex.eqToIso hn ≪≫ Subcomplex.topIso K
  have he : e.hom = (skeletonOfMono i n).ι := rfl
  have hi : i ≫ e.inv = skeletonBase i n := by
    apply (cancel_mono e.hom).1
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, he]
    rfl
  let f := e.inv ≫ S.sourceMap
  have hboundary : i ≫ f = a ≫ pinchedClosedPrecomposition A D S.denominator := by
    change i ≫ e.inv ≫ S.sourceMap = _
    rw [← Category.assoc, hi, S.boundary]
  have hsquare : f ≫ pinchedHomChainMap ((inclusion A D P).map S.source y) =
      S.quotientMap := by
    change (e.inv ≫ S.sourceMap) ≫ _ = _
    rw [Category.assoc, S.square, ← Category.assoc, ← he, e.inv_hom_id, Category.id_comp]
  let H := stableHomotopyRetarget S.homotopy rfl hsquare.symm
  refine {
    source := S.source
    denominator := S.denominator
    denominator_mem := S.denominator_mem
    filler := f
    boundary := hboundary
    comparison := H
    fixed := ?_ }
  exact (congrArg (fun h => (i ▷ (Δ[1] : SSet.{max u v})) ≫ h)
    (homotopyRetarget_h S.homotopy rfl hsquare.symm)).trans S.fixed

/-- 任意の有限単体集合対の厳密係数正方形は、共通閉分母後の境界固定充填を持つ。 -/
theorem dgCoefficientFinitePairs_nonempty [IsDGPretriangulated A D] [Mono i] [K.Finite]
    (hP : localKFlat A D P)
    (ha : a ≫ pinchedHomChainMap ((inclusion A D P).map x y) = i ≫ g) :
    Nonempty (DGCoefficientRelativeFiller A D P i x y a g) := by
  obtain ⟨n, hn⟩ := finiteRelativeSkeleton_exists_top i
  obtain ⟨S⟩ := dgCoefficientSkeletalStage_nonempty A D P i x y a g hP ha n
  exact ⟨DGCoefficientSkeletalStage.toRelativeFiller A D P i x y a g S hn⟩

end SerrePositivity.InfinityCategories
