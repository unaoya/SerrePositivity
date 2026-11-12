module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
概要：一点を右因子とする fat join の写像円柱表示。
方針：最初の pushout で同型となる円柱包含を消去し、残る pushout の直積の点を除く。
規約：モノイダル単位と標準零単体は厳密に同じとは扱わない。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、終域が一点の場合の写像円柱比較の同値性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：右因子が一点の fat join は円柱の一端を一点へ貼る pushout。
方針：最初の pushout の左包含が同型であることを使い、二つ目の pushout の対象を移す。
規約：この段階では右側の点の直積因子を円柱に残す。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、fat join の通常の写像円柱表示への一段目。 -/
lemma fatJoinPoint_isPushout (X : SSet.{u}) :
    IsPushout (SSet.ι₁ (X := X) ▷ (Δ[0] : SSet.{u}))
      (snd X (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder X Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr X Δ[0]) := by
  let j := pushout.inl (SSet.ι₀ (X := X) ▷ (Δ[0] : SSet.{u})) (fst X Δ[0])
  have : IsIso j := (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  apply (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd X (Δ[0] : SSet.{u})) (snd X Δ[0])).of_iso
    (Iso.refl _) (asIso j).symm (Iso.refl _) (Iso.refl _)
  · change ((SSet.ι₁ (X := X) ▷ (Δ[0] : SSet.{u})) ≫ j) ≫ inv j = 𝟙 _ ≫ _
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp
  · change _ ≫ 𝟙 _ = inv j ≫ (j ≫ _)
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp, Category.comp_id]
  · rfl

/-- 概要：右端に点を持つ円柱を通常の区間付き X と同定する。
方針：標準零単体の直積因子を射影で除き、区間を左因子に交換する。
規約：順方向の射は点の射影に続く対称性。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、写像円柱の円柱部分の同定。 -/
noncomputable def fatJoinPointCylinderIso (X : SSet.{u}) :
    (X ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[0] : SSet.{u}) ≅ (Δ[1] : SSet.{u}) ⊗ X :=
  asIso (fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u})) ≪≫ (β_ X (Δ[1] : SSet.{u}))

/-- 概要：通常の区間付き X から一点との fat join への標準射。
方針：右の点を補う円柱同型の逆に fat join の円柱包含を合成する。
規約：一端を一点に貼る。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、終域が一点の場合の比較の円柱部分。 -/
noncomputable def fatJoinPointPrism (X : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin X (Δ[0] : SSet.{u}) :=
  (fatJoinPointCylinderIso X).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder X Δ[0]

/-- 概要：一点との fat join は通常の写像円柱の pushout として表示できる。
方針：円柱の点の因子を同型で除き、貼り合わせの点への射を終対象性で同定する。
規約：X から標準零単体への射 f は任意でよい。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、一般の fat join 比較を写像円柱へ移す表示。 -/
lemma fatJoinPointPrism_isPushout {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f (fatJoinPointPrism X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr X Δ[0]) := by
  apply (fatJoinPoint_isPushout X).of_iso (asIso (fst X (Δ[0] : SSet.{u})))
    (fatJoinPointCylinderIso X) (Iso.refl _) (Iso.refl _)
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, s⟩
    rfl
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · change _ ≫ 𝟙 _ = (fatJoinPointCylinderIso X).hom ≫
      ((fatJoinPointCylinderIso X).inv ≫ _)
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rfl

/-- 概要：一点を終域とする射の写像円柱は一点との fat join と同型。
方針：二つの pushout の普遍性による標準同型を取る。
規約：順方向は写像円柱から fat join への射。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、写像円柱比較の始域の模型変更。 -/
noncomputable def mappingCylinderFatJoinPointIso {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin X (Δ[0] : SSet.{u}) :=
  (fatJoinPointPrism_isPushout f).isoPushout.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
