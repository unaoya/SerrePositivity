module

public import SerrePositivity.KST.Descent.ComponentSplit

/-!
# 残りの閉和の整成分による有限被覆

## 概要
選んだ一成分を除いた整成分から、残りの被約閉部分への実際の閉被覆を構成する。

## 方針
閉集合の包含から因子分解し、元の対象への閉包含の点の単射性で被覆を確認する。

## 規約
成分の数の減少は残りを覆う元の成分の数で測る。

## 使われ方
論文 補題 3.3・定理 3.1 の次元を固定した有限閉和の帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} (X : FiniteTypeSchemes S) [NoetherianSpace X.obj.left]
variable (c d : IrreducibleComponentIndex X)

/-- 概要：他の成分の台は残りの閉和に含まれる（論文 定理 3.1）。
方針：残りを定める集合の和へ、その成分を入れる。
規約：成分の相異性を明示する。
使われ方：整成分の包含を残りの被約閉部分へ因子分解する。 -/
theorem irreducibleComponent_le_remainder (different : d ≠ c) :
    irreducibleComponentClosedSet X d ≤ componentRemainder X c := by
  intro x hx
  refine Set.mem_sUnion.mpr ⟨d.val, ⟨d.property, ?_⟩, hx⟩
  intro h
  apply different
  exact Subtype.ext (Set.mem_singleton_iff.mp h)

/-- 概要：他の整成分から残りの被約閉部分への指定包含（論文 定理 3.1）。
方針：閉集合の包含による被約閉部分スキーム間の射を用いる。
規約：元の対象と同じ基底 S 上の射。
使われ方：残りを覆う有限な整成分の族。 -/
noncomputable def componentToRemainder (different : d ≠ c) : integralComponent X d ⟶
    reducedClosedAsFiniteType X (componentRemainder X c) :=
  reducedClosedMapOfLE X (irreducibleComponent_le_remainder X c d different)

/-- 概要：残りへの射を元の対象へ合成すると元の成分の包含（論文 定理 3.1）。
方針：閉集合間の包含の合成公式を使う。
規約：幾何学的な指定射の等式。
使われ方：閉埋め込み性と残りの被覆の判定。 -/
@[reassoc (attr := simp)] theorem componentToRemainder_comp_inclusion (different : d ≠ c) :
    componentToRemainder X c d different ≫
        reducedClosedAsFiniteTypeInclusion X (componentRemainder X c) =
      integralComponentInclusion X d :=
  reducedClosedMapOfLE_comp_inclusion X _

/-- 概要：他の成分から残りへの射は閉埋め込み（論文 補題 3.3）。
方針：元の対象への合成が成分の閉包含であることから判定する。
規約：点集合の包含だけではなくスキームの閉埋め込み。
使われ方：残りに対する閉和の貼り合わせ。 -/
instance componentToRemainder_isClosedImmersion (different : d ≠ c) :
    IsClosedImmersion (componentToRemainder X c d different).hom.left := by
  have : IsClosedImmersion ((componentToRemainder X c d different).hom.left ≫
      (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)).hom.left) := by
    have h := congrArg (fun k ↦ k.hom.left) (componentToRemainder_comp_inclusion X c d different)
    have closed : IsClosedImmersion (integralComponentInclusion X d).hom.left := inferInstance
    exact (congrArg (fun k ↦ IsClosedImmersion k) h).mpr closed
  exact IsClosedImmersion.of_comp (componentToRemainder X c d different).hom.left
    (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)).hom.left

/-- 概要：残りの被約閉部分は他の整成分の像で覆われる（論文 定理 3.1）。
方針：各点の元の対象での像を含む成分を選び、包含の点の単射性で戻す。
規約：添字は一成分を除いた有限集合で、空の残りも含む。
使われ方：整成分の有限被覆の個数を減らす帰納の実際の被覆。 -/
theorem componentToRemainder_covering :
    ⋃ d : {d : IrreducibleComponentIndex X // d ≠ c},
      Set.range (componentToRemainder X c d.val d.property).hom.left = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  let j := reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)
  have hy : j.hom.left y ∈ componentRemainder X c := by
    change reducedClosedInclusion (componentRemainder X c) y ∈
      (componentRemainder X c : Set X.obj.left)
    rw [← range_reducedClosedInclusion (componentRemainder X c)]
    exact Set.mem_range_self y
  obtain ⟨D, hD, hyD⟩ := Set.mem_sUnion.mp hy
  let d : IrreducibleComponentIndex X := ⟨D, hD.1⟩
  have hd : d ≠ c := by
    intro h
    apply hD.2
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val h)
  have hyRange : j.hom.left y ∈ Set.range (integralComponentInclusion X d).hom.left := by
    rw [range_integralComponentInclusion]
    exact hyD
  obtain ⟨z, hz⟩ := hyRange
  refine Set.mem_iUnion.mpr ⟨⟨d, hd⟩, z, j.hom.left.isClosedEmbedding.injective ?_⟩
  have fac := congrArg (fun k : integralComponent X d ⟶ X ↦ k.hom.left z)
    (componentToRemainder_comp_inclusion X c d hd)
  exact fac.trans hz

end SerrePositivity.KST.Descent
