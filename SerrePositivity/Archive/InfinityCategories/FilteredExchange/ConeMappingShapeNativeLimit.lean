module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeMappingShapePushout
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeMappingKanObjects
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareLimits

/-!
概要：形状の接着で得た元の固定頂点の錐空間を、𝒮 の native な極限錐の頂点にする。
方針：単射な第二境界側を第一脚に置き、元の引き戻し正方形と Kan fibration 性を使う。
規約：元の全錐空間・頂点・二部分への制限を保持。使われ方：有限形状の交換の帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (x : X _⦋0⦌)
local notation "r" => normalizedConeRestrictionKanMap (j ≫ p) g (conePushoutBoundary_eq hp p) x
local notation "s" => coneRestrictionKanMap (i ≫ p) f x

/-- 元の全錐空間を頂点とし、第二部分・第一部分の順の制限を持つ native な錐。 -/
def coneMappingShapePushoutNativeCone : JoinCone
    (kanDiagramCoherentNerve (kanPullbackDiagram r s)) :=
  spaceSquareCone (K := coneMappingKanObject p x) r s
    (coneRestrictionFiberMap p j x) (coneRestrictionFiberMap p i x)
    (coneMappingShapePushout_isPullback hp p x).flip

/-- 単射な境界側があれば、元の全錐空間の頂点を持つこの錐は 𝒮 の極限錐。 -/
lemma coneMappingShapePushoutNativeCone_isLimit [Mono g] :
    IsLimitCone (coneMappingShapePushoutNativeCone hp p x) := by
  have : Fibration (show (coneMappingKanObject (j ≫ p) x).obj ⟶
      (coneMappingKanObject (f ≫ (i ≫ p)) x).obj from r) :=
    coneMappingShapePushout_right_fibration hp p x
  exact spaceSquareCone_isLimit (K := coneMappingKanObject p x) r s
    (coneRestrictionFiberMap p j x) (coneRestrictionFiberMap p i x)
    (coneMappingShapePushout_isPullback hp p x).flip

/-- native な錐の頂点は、元の指定頂点の全錐空間の頂点そのもの。 -/
lemma coneMappingShapePushoutNativeCone_vertex :
    (coneMappingShapePushoutNativeCone hp p x).vertex =
      coherentNerveVertex (coneMappingKanObject p x) :=
  spaceSquareCone_vertex (K := coneMappingKanObject p x) r s
    (coneRestrictionFiberMap p j x) (coneRestrictionFiberMap p i x)
    (coneMappingShapePushout_isPullback hp p x).flip

end SerrePositivity.InfinityCategories.F2
