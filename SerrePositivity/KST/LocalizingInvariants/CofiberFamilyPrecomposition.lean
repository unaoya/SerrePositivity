module

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyComparison

/-!
概要：元の選択された cofiber 全族は、任意のパラメータ制限と関手同型で可換する。
方針：両方を同じ普遍 cofiber 関手との合成に比較する。
規約：底辺の元の制限を保持。使われ方：lax 余単位の cofiber を Verdier 包含へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily

def precompositionIso {A B X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (i : B ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X a) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (i ≫ a)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (compositionIso X a) i
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X a) ((i ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _)) := by
    simpa only [Category.assoc] using h
  exact e ≪≫ (compositionIso X (i ≫ a)).symm

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
