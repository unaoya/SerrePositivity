module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
概要：基底上の単体集合を inner anodyne な射で quasicategory に置換する。
方針：内ホーンの小対象論法による因子分解を使い、inner fibration の始域の充填性を得る。
規約：基底が quasicategory のときだけ置換先の quasicategory 性を主張する。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、写像円柱比較の因子の置換。

対応節は Kerodon 4.1（Tag 01B8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 概要：inner anodyne な射は単射。
方針：内ホーンのセル分解に単射の各閉性を適用する。
規約：単体集合の充填性は仮定しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、置換の包含に沿う図式の延長。 -/
lemma mono_of_innerAnodyne {X Y : SSet.{u}} (i : X ⟶ Y)
    (hi : innerAnodyneExtensions i) : Mono i := by
  have h : innerAnodyneExtensions.{u} ≤ monomorphisms SSet := by
    rw [innerAnodyneExtensions_eq_retracts_transfiniteCompositions]
    rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact innerHornInclusions_le_monomorphisms
  exact h _ hi

/-- 概要：任意の単体集合の射は inner anodyne な射と inner fibration に分解できる。
方針：内ホーンの小対象論法から得られる関手的因子分解を取る。
規約：合成の一致は厳密な等式。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、基底上の quasicategory の置換の構成。 -/
lemma exists_innerAnodyne_innerFibration_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      innerAnodyneExtensions i ∧ InnerFibration p ∧ i ≫ p = f := by
  let d := factorizationData innerHornInclusions.rlp.llp innerHornInclusions.rlp f
  exact ⟨d.Z, d.i, d.p, d.hi, ⟨d.hp⟩, d.fac⟩

/-- 概要：quasicategory への射を保ったまま始域を inner anodyne な射で quasicategory に置換できる。
方針：内ホーンの因子分解の右因子から始域の quasicategory 性を導く。
規約：元の X は任意。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、両端 fiber 上の図式の置換。 -/
lemma exists_quasicategory_resolution_over {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      innerAnodyneExtensions i ∧ Quasicategory Z ∧ InnerFibration p ∧ i ≫ p = f := by
  obtain ⟨Z, i, p, hi, hp, h⟩ := exists_innerAnodyne_innerFibration_factorization f
  have : InnerFibration p := hp
  exact ⟨Z, i, p, hi, quasicategory_of_innerFibration p, hp, h⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations
