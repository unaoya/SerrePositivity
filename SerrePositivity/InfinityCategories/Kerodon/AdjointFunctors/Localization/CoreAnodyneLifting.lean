module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration

/-!
概要：core に入る指定図式は、anodyne 射に沿って底を固定したまま延長できる。
方針：同値を持ち上げる関手の core は Kan fibration なので、元の正方形を持ち上げる。
規約：追加のモデル圏仮定を置かない。使われ方：可逆区間の相対的な延長と商の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

lemma exists_coreAnodyne_lift {A B X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (j : A ⟶ B)
    (hj : anodyneExtensions j) (f : A ⟶ X) (g : B ⟶ Y)
    (hf : ∀ s : A _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)))
    (hg : ∀ s : B _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (g.app (Opposite.op ⦋1⦌) s)))
    (h : f ≫ p = j ≫ g) : ∃ l : B ⟶ X, j ≫ l = f ∧ l ≫ p = g := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting p hp
  have : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) := by
    rw [anodyneExtensions_eq_llp_rlp] at hj
    exact hj _ ((fibration_iff _).mp inferInstance)
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift f hf) j (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift g hg) := ⟨by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι).mp
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι, h]⟩
  refine ⟨sq.lift ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι]
  · rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc, sq.fac_right,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι]

/-- Kan な始域からの射の全ての辺は可逆。 -/
lemma kanSource_map_invertible {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X)
    (s : A _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) :=
    @IsGroupoid.all_isIso (hoFunctor.obj A) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid A) _ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map f))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)) rfl).mp (hs.map f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
