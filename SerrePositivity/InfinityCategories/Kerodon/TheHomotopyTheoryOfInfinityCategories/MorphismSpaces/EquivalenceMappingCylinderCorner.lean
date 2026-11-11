module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceMappingCylinderMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionCellClosure

/-!
概要：可逆な写像円柱の相対的な比較射。
方針：始域の変化を先に pushout し、写像円柱の端点の逆像を使う。
規約：元の比較を自然な単射へ置き換えてセルを貼るための補助模型。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限のセルによる比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：写像円柱の始域の変化を指定した相対的な始域。
方針：残った端点に沿って新しい始域を貼る。
規約：f は元の比較射、a は始域の変化。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の一段の相対セル。 -/
noncomputable def equivalenceMappingCylinderCorner {A B A' : SSet.{u}}
    (f : A ⟶ B) (a : A ⟶ A') : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f) a

/-- 概要：可換正方形から写像円柱の相対的な比較射を作る。
方針：元の写像円柱の射と新しい端点の包含を貼り合わせる。
規約：始域の変更部分を既に含めた比較射。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の相対セルの貼り合わせ。 -/
noncomputable def equivalenceMappingCylinderCornerMap {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    equivalenceMappingCylinderCorner f a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder f' :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f f' a b h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f') (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderIn_map f f' a b h)

/-- 概要：始域と終域の比較が単射なら相対写像円柱の比較も単射。
方針：端点の逆像が一致することから二つの単射の和を取る。
規約：元の射 f、f' の単射性や同値性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の相対セルの包含。 -/
instance equivalenceMappingCylinderCornerMap_mono {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    [Mono a] [Mono b] : Mono (equivalenceMappingCylinderCornerMap f f' a b h) := by
  let P := IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f) a
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderIn_map_isPullback f f' a b h
  have he : P.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f f' a b h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f') Q.w = equivalenceMappingCylinderCornerMap f f' a b h := by
    apply P.hom_ext
    · rw [P.inl_desc, equivalenceMappingCylinderCornerMap, pushout.inl_desc]
    · rw [P.inr_desc, equivalenceMappingCylinderCornerMap, pushout.inr_desc]
  rw [← he]
  exact P.desc_mono_of_isPullback Q

/-- 概要：二つの比較射が前合成の同値条件を満たせば相対写像円柱の比較も満たす。
方針：元の端点の pushout の同値条件を新しい端点の条件から消去する。
規約：始域と終域の変化の単射性はこの同値条件に不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各相対セルの同値条件。 -/
lemma isPrecompositionEquivalence_equivalenceMappingCylinderCornerMap {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (equivalenceMappingCylinderCornerMap f f' a b h) := by
  have hI := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn f).1 hf
  have hI' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn f').1 hf'
  have hi := hI.of_isPushout (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f) a)
  apply hi.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f) a ≫
      equivalenceMappingCylinderCornerMap f f' a b h)
  rw [equivalenceMappingCylinderCornerMap, pushout.inr_desc]
  exact hI'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
