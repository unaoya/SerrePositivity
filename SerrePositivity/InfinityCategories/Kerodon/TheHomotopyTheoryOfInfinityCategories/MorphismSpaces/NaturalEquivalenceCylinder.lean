module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceMappingCylinderFunctor

/-!
概要：自然変換を可逆な写像円柱の自然な単射へ置き換える。
方針：自然変換を射の圏への関手と見て写像円柱の関手を合成する。
規約：元の自然変換の成分の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと骨格の余極限。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：自然変換を射の圏への関手として表す。
方針：各成分を対象、自然性の正方形を射にする。
規約：始域の圏 C は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の自然な写像円柱。 -/
def naturalTransformationArrowFunctor {C : Type v} [Category C]
    {F G : C ⥤ SSet.{u}} (t : F ⟶ G) : C ⥤ Arrow SSet.{u} where
  obj A := Arrow.mk (t.app A)
  map f := Arrow.homMk (F.map f) (G.map f) (t.naturality f)
  map_id A := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- 概要：自然変換の各成分の可逆な写像円柱の関手。
方針：射の圏への関手と写像円柱の関手を合成する。
規約：始域の圏 C は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然な単射への置換。 -/
noncomputable def naturalEquivalenceCylinder {C : Type v} [Category C]
    {F G : C ⥤ SSet.{u}} (t : F ⟶ G) : C ⥤ SSet.{u} :=
  naturalTransformationArrowFunctor t ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderFunctor

/-- 概要：元の関手から写像円柱の関手への端点の包含は自然変換。
方針：写像円柱の残った端点の自然性を使う。
規約：各成分は単射である。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の比較射の置換。 -/
noncomputable def naturalEquivalenceCylinderIn {C : Type v} [Category C]
    {F G : C ⥤ SSet.{u}} (t : F ⟶ G) : F ⟶ naturalEquivalenceCylinder t where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn (t.app A)
  naturality A B f := by
    change F.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn (t.app B) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn (t.app A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap (t.app A) (t.app B) (F.map f) (G.map f)
          (t.naturality f).symm
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderIn_map _ _ _ _ (t.naturality f).symm).symm

/-- 概要：写像円柱の関手は二つの元の関手が保つ余極限を保つ。
方針：元の二つの関手と円柱の点ごとの pushout による余極限保存を使う。
規約：指定形 J の余極限保存だけを仮定する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族と骨格。 -/
instance naturalEquivalenceCylinder_preservesColimitsOfShape
    {C : Type v} [Category C] {F G : C ⥤ SSet.{u}} (t : F ⟶ G)
    (J : Type*) [Category* J] [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (naturalEquivalenceCylinder t) := by
  let A := naturalTransformationArrowFunctor t
  have : PreservesColimitsOfShape J (A ⋙ Arrow.leftFunc) := by
    change PreservesColimitsOfShape J F
    infer_instance
  have : PreservesColimitsOfShape J (A ⋙ Arrow.rightFunc) := by
    change PreservesColimitsOfShape J G
    infer_instance
  have : PreservesColimitsOfShape J (A ⋙ (Arrow.leftFunc ⋙ tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)) := by
    change PreservesColimitsOfShape J (F ⋙ tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J
    (Functor.whiskerLeft A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderZeroNat)
    (Functor.whiskerLeft A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderArrowNat)
    (Functor.whiskerLeft A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderInlNat)
    (Functor.whiskerLeft A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderInrNat)
    (fun _ ↦ IsPushout.of_hasPushout _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
