module
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.EpsilonCellHomotopy
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.NativeTarget

/-!
概要：固定 resolved 族の native ε core への作用に必要な対象等号。
方針：工程 1 の指定頂点比較を、cell ε core の可逆比較の剛性に代入する。
規約：この必要条件の固定族での成立・不成立も、最終 map の不存在も未主張。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped Simplicial
variable (R : Type u) [CommRing R] [Nontrivial R]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
  (A B : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => dgKappaConeInput_unconditional' R A κ hκ
local notation "IB" => dgKappaConeInput_unconditional' R B κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "CB" => DGKappaCone R B IB
local notation "PA" => Source R CA
local notation "PB" => Source R CB
local notation "SA" => resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)
local notation "SB" => resolvedDGNullObjects R CB (dgKappaConePerfectObjects R B IB)

/-- 工程 1 の頂点を ε core 内で比較しても、null 対象上の像は実際の対象として一致する必要がある。 -/
lemma dgSuspensionResolved_obj_eq_of_nativeHom
    (H : dgFunctorNativeMappingSpace R A B ⟶ dgSuspensionResolvedEpsilonCore R κ hκ A B)
    (f g : A ⟶ B)
    (e : VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down))
    (hf : VertexIso (X := dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B f.down))
      (dgSuspensionResolvedEpsilonVertex R κ hκ A B f))
    (hg : VertexIso (X := dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B g.down))
      (dgSuspensionResolvedEpsilonVertex R κ hκ A B g))
    (b : SA) :
    (dgSuspensionUnconditionalMapData R κ hκ f).resolved.obj b.val =
      (dgSuspensionUnconditionalMapData R κ hκ g).resolved.obj b.val :=
  quotientEpsilonCell_nativeMap_obj_eq R PA CB SA SB b H
    (dgSuspensionResolvedEpsilonObject R κ hκ A B f)
    (dgSuspensionResolvedEpsilonObject R κ hκ A B g) e hf hg

end SerrePositivity.InfinityCategories
