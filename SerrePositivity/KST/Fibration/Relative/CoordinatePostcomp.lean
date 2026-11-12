module
public import SerrePositivity.KST.Fibration.Relative.FiniteCoordinates
public import SerrePositivity.KST.Fibration.WeakStringFinitePostNaturality
public import SerrePositivity.KST.Fibration.WeakStringRelativeMultiPostcomp

/-!
概要：全単体的な有限積座標の後合成を、元の実有限積写像と照合する。
方針：全 W 列の自然変換を同じ加法性同型で輸送し、既存の成分公式で同定する。
規約：局所化後の自然変換であり、SSet の対角に適用しない。
使われ方：包含側と周囲側を同時に保つ K-B2 の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：有限積座標間の全単体的後合成。方針：元の自然変換を共役する。
規約：比較の逆は局所化内。使われ方：核側と周囲側の同時比較。 -/
def finiteCoordinatePostcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    finiteCoordinateDiagram (f ≫ q : A ⟶ C) r ⟶ finiteCoordinateDiagram q r :=
  (finiteComparisonNatIso (f ≫ q : A ⟶ C) r).inv ≫
    Functor.whiskerRight (weakStringMultiPostcomp f q (r + 1))
      AnodyneHomotopy.anodyneQ ≫ (finiteComparisonNatIso q r).hom

/-- 概要：同じ比較は後合成にも自然。方針：同型の逆律を使う。
規約：全面・全退化を含む自然変換の等号。使われ方：全図式での比較。 -/
theorem finiteComparison_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    Functor.whiskerRight (weakStringMultiPostcomp f q (r + 1))
        AnodyneHomotopy.anodyneQ ≫ (finiteComparisonNatIso q r).hom =
      (finiteComparisonNatIso (f ≫ q : A ⟶ C) r).hom ≫ finiteCoordinatePostcomp f q r := by
  simp [finiteCoordinatePostcomp]

/-- 概要：輸送した後合成は元の初期頂点と核値 cofiber の実積写像。
方針：既存の加法性自然性を同じ比較同型で消去する。
規約：零長を含む全長・全正反復。使われ方：輸送した作用の具体的回収。 -/
theorem finiteCoordinatePostcomp_app {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (finiteCoordinatePostcomp f q r).app (Opposite.op ⦋n⦌) =
      AnodyneHomotopy.anodyneQ.map (weakStringFinitePostMap f q n (r + 1)) := by
  apply (cancel_epi (finiteComparisonIso (f ≫ q : A ⟶ C) n r).hom).1
  have hn := congrArg (fun t => t.app (Opposite.op ⦋n⦌))
    (finiteComparison_postcomp f q r)
  change AnodyneHomotopy.anodyneQ.map
      ((SConstruction.multiRealizationFunctor (r + 1)).map
        (weakStringPostExact f q ⦋n⦌)) ≫
      AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q n (r + 1)) =
    (finiteComparisonIso (f ≫ q : A ⟶ C) n r).hom ≫
      (finiteCoordinatePostcomp f q r).app (Opposite.op ⦋n⦌) at hn
  rw [← hn]
  dsimp only [finiteComparisonIso, asIso]
  simpa only [Functor.map_comp] using
    weakStringFiniteComparison_postcomp f q n r

end SerrePositivity.KST.Fibration.Relative
