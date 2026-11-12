module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalPullbackPathHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の interval 引き戻しの指定 path 円柱を任意の始域射で制限する。
方針：積の入れ替えと uncurry の前合成を全単体で計算する。
規約：元の全 path を保持。使われ方：模型比較に沿った可換円柱の識別。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定 path 円柱の始域制限は元の同じ全 path 座標の円柱。 -/
lemma intervalPullbackPathHomotopy_precomp_cylinder {X Y Z A : SSet.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : A ⟶ intervalPullback f g) :
    (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) h).h =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ uncurry (h ≫ intervalPullbackPath f g) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
