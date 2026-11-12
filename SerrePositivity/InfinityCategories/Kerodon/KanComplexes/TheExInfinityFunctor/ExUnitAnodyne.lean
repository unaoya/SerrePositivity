module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingRegular
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex の単位の anodyne 性

概要：全ての単体集合 X に対して、明示的に構成した単位 X→Ex(X) は anodyne 拡張である。
方針：正則 pairing から像の包含の anodyne 性を得て、単射な単位の像への同型を合成する。
規約：Moss 2020 Theorem 22。regular pairing は本レーンで証明し Mathlib の一般定理を使う。
使われ方：Ex∞ の単位の anodyne 性と Kan 置換の構成。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory

/--
概要：Ex の単位の像の包含は anodyne 拡張である。
方針：構成した正則 pairing に Mathlib の一般定理を適用する。
規約：Moss 2020 Theorem 22 の像の包含の形。
使われ方：元の単位の anodyne 性。
-/
theorem exUnitRange_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (SSet.Subcomplex.range (exUnitAt X)).ι :=
  (exPairing X).anodyneExtensions

/--
概要：明示的に構成した Ex の単位は anodyne 拡張である。
方針：像への同型と正則 pairing を持つ像の包含を合成する。
規約：Moss 2020 Theorem 22。
使われ方：Ex∞ への各遷移とその合成の anodyne 性。
-/
@[kerodon 00Z2]
theorem exUnitAt_anodyne (X : SSet.{u}) : SSet.anodyneExtensions (exUnitAt X) := by
  rw [← SSet.Subcomplex.toRange_ι (exUnitAt X)]
  exact SSet.anodyneExtensions.comp_mem _ _
    (SSet.anodyneExtensions.of_isIso _) (exUnitRange_anodyne X)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
