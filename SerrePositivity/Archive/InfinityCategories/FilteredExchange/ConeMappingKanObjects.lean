module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeMappingRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport

/-!
概要：頂点固定の錐空間と元の制限を Kan 対象と射に束ねる。
方針：構成済みの Kan 性を添え、台の射は元の制限そのものとする。
規約：元の頂点・図式・全単体を保持。使われ方：形状の接着を 𝒮 の native 極限にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の固定頂点の錐空間を台に持つ Kan 対象。 -/
def coneMappingKanObject {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) (x : X _⦋0⦌) :
    KanObject.{u} := ⟨coneMappingSpace p x, inferInstance⟩

/-- 元の部分形状への制限を、同じ錐空間の Kan 対象間の射とする。 -/
def coneRestrictionKanMap {K L X : SSet.{u}} [Quasicategory X] (p : K ⟶ X)
    (i : L ⟶ K) (x : X _⦋0⦌) :
    coneMappingKanObject p x ⟶ coneMappingKanObject (i ≫ p) x := coneRestrictionFiberMap p i x

/-- 図式の表示だけを移した元の制限を、同じ Kan 対象間の射とする。 -/
def normalizedConeRestrictionKanMap {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (i : L ⟶ K) {q : L ⟶ X} (hi : i ≫ p = q) (x : X _⦋0⦌) :
    coneMappingKanObject p x ⟶ coneMappingKanObject q x := normalizedConeRestrictionFiber p i hi x

end SerrePositivity.InfinityCategories.F2
