module

public import SerrePositivity.KST.Descent.NoetherianReduction
public import Mathlib.Topology.NoetherianSpace

/-!
# 有限型対象の既約成分の整な閉構造

## 概要
既約成分を実際の整な有限型閉部分スキームとし、Noether の場合に有限被覆を得る。

## 方針
各既約成分の消滅イデアル層を使い、台との同相から既約性を移す。

## 規約
元の対象の被約性は不要。有限性には基礎空間の Noether 性を明示する。

## 使われ方
論文 補題 3.3・定理 3.1 の「整 → 被約」の有限な閉和による帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} (X : FiniteTypeSchemes S)

/-- 概要：既約成分の添字（論文 定理 3.1）。
方針：基礎空間の極大既約部分集合をそのまま用いる。
規約：空スキームでは添字も空。
使われ方：整な有限型閉部分の有限族。 -/
abbrev IrreducibleComponentIndex := irreducibleComponents X.obj.left

/-- 概要：Noether 空間の既約成分の添字は有限（論文 補題 3.3）。
方針：Mathlib の既約成分の有限性を部分型へ移す。
規約：添字の非空性は仮定しない。
使われ方：有限閉和の帰納。 -/
instance irreducibleComponentIndex_finite [NoetherianSpace X.obj.left] :
    Finite (IrreducibleComponentIndex X) :=
  NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- 概要：一つの既約成分を閉集合として束ねる（論文 定理 3.1）。
方針：極大既約部分集合の閉性を使う。
規約：構造層を入れる前の台。
使われ方：整な閉部分スキームの構成。 -/
def irreducibleComponentClosedSet (c : IrreducibleComponentIndex X) : Closeds X.obj.left :=
  ⟨c.val, isClosed_of_mem_irreducibleComponents _ c.property⟩

/-- 概要：既約成分に被約閉構造を入れた有限型対象（論文 定理 3.1）。
方針：消滅イデアル層による被約閉部分スキームを用いる。
規約：元の対象と同じ基底 S 上の有限型対象。
使われ方：整な場合の帰納仮定を適用する成分。 -/
noncomputable def integralComponent (c : IrreducibleComponentIndex X) : FiniteTypeSchemes S :=
  reducedClosedAsFiniteType X (irreducibleComponentClosedSet X c)

/-- 概要：整な成分の実際の閉包含（論文 定理 3.1）。
方針：被約閉部分スキームの包含を使う。
規約：同じ基底上の射として保持する。
使われ方：閉和の降下と元の対象との比較。 -/
noncomputable def integralComponentInclusion (c : IrreducibleComponentIndex X) :
    integralComponent X c ⟶ X :=
  reducedClosedAsFiniteTypeInclusion X (irreducibleComponentClosedSet X c)

/-- 概要：構成した各成分は整スキーム（論文 定理 3.1）。
方針：台の既約性を同相で移し、被約性と組み合わせる。
規約：非空性は既約成分の定義から得る。
使われ方：「整」の場合の結論を各成分へ適用する。 -/
instance integralComponent_isIntegral (c : IrreducibleComponentIndex X) :
    IsIntegral (integralComponent X c).obj.left := by
  change IsIntegral (reducedClosedSubscheme (irreducibleComponentClosedSet X c))
  have : IrreducibleSpace (irreducibleComponentClosedSet X c) :=
    isIrreducible_iff_irreducibleSpace.mp c.property.1
  have : IrreducibleSpace (reducedClosedSubscheme (irreducibleComponentClosedSet X c)) :=
    (reducedClosedHomeo (irreducibleComponentClosedSet X c)).irreducibleSpace_iff.mpr
      inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- 概要：各整成分の包含は閉埋め込み（論文 補題 3.3）。
方針：被約閉構造の包含の性質を使う。
規約：有限型の包みを保つ。
使われ方：二つの閉部分の被覆の構成。 -/
instance integralComponentInclusion_isClosedImmersion (c : IrreducibleComponentIndex X) :
    IsClosedImmersion (integralComponentInclusion X c).hom.left :=
  reducedClosedInclusion_isClosedImmersion _

/-- 概要：整な成分の包含の像は指定した既約成分（論文 定理 3.1）。
方針：被約閉構造の台の同定を使う。
規約：基礎空間の集合としての等式。
使われ方：被覆と交わりの真閉性。 -/
theorem range_integralComponentInclusion (c : IrreducibleComponentIndex X) :
    Set.range (integralComponentInclusion X c).hom.left = c.val :=
  range_reducedClosedInclusion _

/-- 概要：整な成分の閉包含の像は全体を覆う（論文 定理 3.1）。
方針：任意の点を含む既約成分を選ぶ。
規約：この被覆の等式そのものには Noether 性は不要。
使われ方：Noether の場合の有限閉被覆。 -/
theorem integralComponent_covering :
    ⋃ c : IrreducibleComponentIndex X, Set.range (integralComponentInclusion X c).hom.left =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [range_integralComponentInclusion]
  exact mem_irreducibleComponent

/-- 概要：各整成分の次元は元の次元以下（論文 定理 3.1）。
方針：台との同相と部分空間の次元単調性を使う。
規約：有限次元は仮定せず、拡張自然数の次元を比較する。
使われ方：次元上界を各整成分へ渡す。 -/
theorem integralComponent_dimension_le (c : IrreducibleComponentIndex X) :
    topologicalKrullDim (integralComponent X c).obj.left ≤ topologicalKrullDim X.obj.left := by
  change topologicalKrullDim (reducedClosedSubscheme (irreducibleComponentClosedSet X c)) ≤ _
  rw [reducedClosedSubscheme_dimension]
  exact topologicalKrullDim_subspace_le X.obj.left _

end SerrePositivity.KST.Descent
