module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiHomology
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
/-!
概要：全基点の π と実評価ホモロジー余錐の照合データを定義する。
方針：元の実脚と transition の自然性を、通常の加群値ホモロジー図式へ保持する。
規約：π の群余極限を仮定せず、各次数の実加群余錐の普遍性を使う。
使われ方：評価の Dold–Kan 比較を元ごとの五条件へ渡す中間データ。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

structure DGBarCompactHomologyCharts (R : Type u) [CommRing R]
    {I : Type u} [PartialOrder I] (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, ((X i).obj ⟶ A.obj)) where
  diagram : ℕ → I ⥤ ModuleCat.{u} R
  cocone : ∀ n, Cocone (diagram n)
  isColimit : ∀ n, IsColimit (cocone n)
  zeroStage : ∀ i, SSet.π₀ (X i).obj ≃ (diagram 0).obj i
  zeroApex : SSet.π₀ A.obj ≃ (cocone 0).pt
  zero_leg : ∀ i y, zeroApex (SSet.π₀.mk ((l i).app _ y)) =
    (cocone 0).ι.app i (zeroStage i (SSet.π₀.mk y))
  zero_transition : ∀ {i j} (h : i ≤ j) y,
    zeroStage j (SSet.π₀.mk ((τ h).app _ y)) =
      (diagram 0).map (homOfLE h) (zeroStage i (SSet.π₀.mk y))
  positiveStage : ∀ n i y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X i).obj n y ≃ (diagram (n + 1)).obj i
  positiveApex : ∀ n z, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup A.obj n z ≃ (cocone (n + 1)).pt
  positive_leg : ∀ n i y a,
    positiveApex n ((l i).app _ y) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l i) y a) =
      (cocone (n + 1)).ι.app i (positiveStage n i y a)
  positive_transition : ∀ n {i j} (h : i ≤ j) y a,
    positiveStage n j ((τ h).app _ y) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (τ h) y a) =
      (diagram (n + 1)).map (homOfLE h) (positiveStage n i y a)
  transport : ∀ n {x y} (e : A.obj.Edge x y) a b,
    positiveApex n x a = positiveApex n y b → _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b

variable {R : Type u} [CommRing R] {I : Type u} [PartialOrder I] [IsFiltered I]
  {X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}} {A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}}
  {τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj)}
  {l : ∀ i : I, ((X i).obj ⟶ A.obj)}
  (H : DGBarCompactHomologyCharts R X A τ l)

def dgBarCompactHomologyUnderlyingIsColimit (n : ℕ) :
    IsColimit ((forget (ModuleCat.{u} R)).mapCocone (H.cocone n)) :=
  isColimitOfPreserves (forget (ModuleCat.{u} R)) (H.isColimit n)

lemma dgBarCompactHomology_jointly_surjective (n : ℕ) (a : (H.cocone n).pt) :
    ∃ i b, (H.cocone n).ι.app i b = a :=
  Types.jointly_surjective_of_isColimit (dgBarCompactHomologyUnderlyingIsColimit H n) a

lemma dgBarCompactHomology_equal_at_stage (n : ℕ) {i j : I}
    (a : (H.diagram n).obj i) (b : (H.diagram n).obj j)
    (h : (H.cocone n).ι.app i a = (H.cocone n).ι.app j b) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      (H.diagram n).map (homOfLE hik) a = (H.diagram n).map (homOfLE hjk) b := by
  obtain ⟨k, f, g, he⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (dgBarCompactHomologyUnderlyingIsColimit H n)).mp h
  change (H.diagram n).map f a = (H.diagram n).map g b at he
  refine ⟨k, leOfHom f, leOfHom g, ?_⟩
  simpa only [Subsingleton.elim (homOfLE (leOfHom f)) f,
    Subsingleton.elim (homOfLE (leOfHom g)) g] using he

lemma dgBarCompactHomology_equal_at_stage_same (n : ℕ) {i : I}
    (a b : (H.diagram n).obj i)
    (h : (H.cocone n).ι.app i a = (H.cocone n).ι.app i b) :
    ∃ (j : I) (hij : i ≤ j),
      (H.diagram n).map (homOfLE hij) a = (H.diagram n).map (homOfLE hij) b := by
  obtain ⟨j, f, he⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (dgBarCompactHomologyUnderlyingIsColimit H n) a b).mp h
  change (H.diagram n).map f a = (H.diagram n).map f b at he
  refine ⟨j, leOfHom f, ?_⟩
  simpa only [Subsingleton.elim (homOfLE (leOfHom f)) f] using he

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
