module
public import SerrePositivity.KST.Fibration.WeakStringFiniteAllLengths
public import SerrePositivity.KST.Fibration.WeakStringFiniteFaces
public import SerrePositivity.KST.Fibration.WeakStringFiniteDegeneracies

/-!
概要：全有限 W 列の初期頂点・連続 cofiber 比較を局所化後の単体的同型に束ねる。
方針：既存の全長・全正反復の加法性同型で元の再添字を有限積座標へ輸送する。
規約：値域は anodyne 局所化。SSet 値の単体的比較や対角実現の同値とは主張しない。
使われ方：K-B2 の全単体的比較の座標法則と、実現へ渡す際の供給境界の確認。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：各次数の実有限積。方針：既存比較の値域を使う。
規約：r は正反復から一を引いた数。使われ方：局所化後の座標対象。 -/
def finiteCoordinates {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) : SSet.{u} :=
  (multiRealizationFunctor (r + 1)).obj
    (closedStableModel (ClosedStablePredicate.top (sInputModel B))) ⊗
      ∏ᶜ (fun _ : Fin n => (multiRealizationFunctor (r + 1)).obj
        (closedStableModel (kernelClosedPredicate q)))

/-- 概要：元の比較を順射に持つ同型。方針：既存の加法性定理を適用。
規約：局所化内のみ。使われ方：全面・全退化の座標輸送。 -/
def finiteComparisonIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    AnodyneHomotopy.anodyneQ.obj ((weakStringMultiRealization q (r + 1)).obj
      (Opposite.op ⦋n⦌)) ≅ AnodyneHomotopy.anodyneQ.obj (finiteCoordinates q n r) := by
  exact @asIso _ _ _ _
    (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q n (r + 1)))
    (weakStringFiniteComparison_localized_isIso q n r)

/-- 概要：有限積座標の全単体作用。方針：元の W 列の作用を同型で共役する。
規約：生の積上の厳密加法を選ばない。使われ方：全単体的局所化比較。 -/
def finiteCoordinateDiagram {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    SimplicialObject SSet.anodyneExtensions.{u}.Localization where
  obj n := AnodyneHomotopy.anodyneQ.obj (finiteCoordinates q n.unop.len r)
  map {n m} θ := (finiteComparisonIso q n.unop.len r).inv ≫
    AnodyneHomotopy.anodyneQ.map ((weakStringMultiRealization q (r + 1)).map θ) ≫
      (finiteComparisonIso q m.unop.len r).hom
  map_id n := by simp
  map_comp θ φ := by simp [Category.assoc]

/-- 概要：元の全 W 列から有限積座標への単体的同型。
方針：同じ比較を各次数に置く。規約：局所化後。使われ方：元の全作用の保持。 -/
def finiteComparisonNatIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    weakStringMultiRealization q (r + 1) ⋙ AnodyneHomotopy.anodyneQ ≅
      finiteCoordinateDiagram q r :=
  NatIso.ofComponents (fun n => finiteComparisonIso q n.unop.len r) (by
    intro n m θ
    simp [finiteCoordinateDiagram])

/-- 概要：全面・全退化の自然性。方針：同型の自然性を読む。
規約：元の有限比較を使う。使われ方：個々の面に限定しない比較。 -/
theorem finiteComparison_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    AnodyneHomotopy.anodyneQ.map ((weakStringMultiRealization q (r + 1)).map θ) ≫
        (finiteComparisonIso q n.unop.len r).hom =
      (finiteComparisonIso q m.unop.len r).hom ≫ (finiteCoordinateDiagram q r).map θ :=
  (finiteComparisonNatIso q r).hom.naturality θ

end SerrePositivity.KST.Fibration.Relative
