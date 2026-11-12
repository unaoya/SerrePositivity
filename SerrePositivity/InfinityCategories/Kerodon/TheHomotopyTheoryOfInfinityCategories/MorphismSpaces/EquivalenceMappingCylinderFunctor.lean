module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceMappingCylinderCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutFunctorColimits
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：可逆な写像円柱を射の圏からの関手にする。
方針：pushout の三つの制限で恒等と合成を比較する。
規約：射の圏の左右の評価関手を用いる。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然な比較射の置換。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：恒等正方形が誘導する写像円柱の射は恒等。
方針：円柱と終域上で比較する。
規約：可換性の証明の選択は問わない。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の関手性。 -/
lemma equivalenceMappingCylinderMap_id {A B : SSet.{u}} (f : A ⟶ B)
    (h : f ≫ 𝟙 B = 𝟙 A ≫ f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f f (𝟙 A) (𝟙 B) h = 𝟙 _ := by
  apply pushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inl,
      Category.comp_id, id_whiskerRight, Category.id_comp]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inr,
      Category.comp_id, Category.id_comp]

/-- 概要：可換正方形の合成からの写像円柱の射は誘導射の合成。
方針：円柱と終域上で二つの合成を比較する。
規約：元の正方形に単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の関手性。 -/
lemma equivalenceMappingCylinderMap_comp {A B A' B' A'' B'' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : f ≫ b = a ≫ f') (h' : f' ≫ b' = a' ≫ f'')
    (hh : f ≫ (b ≫ b') = (a ≫ a') ≫ f'') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f f' a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f' f'' a' b' h' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap f f'' (a ≫ a') (b ≫ b') hh := by
  apply pushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inl, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inl,
      ← Category.assoc, ← comp_whiskerRight]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inr, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inr, Category.assoc]

/-- 概要：可逆な写像円柱は単体集合の射の圏からの関手。
方針：可換正方形を円柱の誘導射へ送る。
規約：元の射の左右の対象は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然変換の置換。 -/
noncomputable def equivalenceMappingCylinderFunctor : Arrow SSet.{u} ⥤ SSet.{u} where
  obj f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder f.hom
  map m := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap _ _ m.left m.right m.w.symm
  map_id f := equivalenceMappingCylinderMap_id f.hom _
  map_comp m n := (equivalenceMappingCylinderMap_comp _ _ _ _ _ _ _ _ _ _).symm

/-- 概要：射の始域の可逆な円柱の零端は自然変換。
方針：端点の自然性を各可換正方形に適用する。
規約：零端を貼り合わせる。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手の pushout。 -/
def equivalenceMappingCylinderZeroNat :
    (Arrow.leftFunc : Arrow SSet.{u} ⥤ SSet.{u}) ⟶
      Arrow.leftFunc ⋙ tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval where
  app f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint f.left false
  naturality _ _ m := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality m.left false

/-- 概要：射そのものは左右の評価関手の間の自然変換。
方針：可換正方形の可換性を使う。
規約：射の圏は単体集合の射の圏。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の関手の pushout。 -/
def equivalenceMappingCylinderArrowNat :
    (Arrow.leftFunc : Arrow SSet.{u} ⥤ SSet.{u}) ⟶ Arrow.rightFunc where
  app f := f.hom
  naturality _ _ m := m.w

/-- 概要：円柱から写像円柱への包含は自然変換。
方針：写像円柱の誘導射の左包含上の計算を使う。
規約：始域の円柱を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手の pushout。 -/
noncomputable def equivalenceMappingCylinderInlNat :
    Arrow.leftFunc ⋙ tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ equivalenceMappingCylinderFunctor.{u} where
  app f := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint f.left false) f.hom
  naturality _ _ m := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inl _ _ m.left m.right m.w.symm).symm

/-- 概要：終域から写像円柱への包含は自然変換。
方針：写像円柱の誘導射の右包含上の計算を使う。
規約：元の射の終域を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手の pushout。 -/
noncomputable def equivalenceMappingCylinderInrNat :
    (Arrow.rightFunc : Arrow SSet.{u} ⥤ SSet.{u}) ⟶ equivalenceMappingCylinderFunctor where
  app f := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint f.left false) f.hom
  naturality _ _ m := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderMap_inr _ _ m.left m.right m.w.symm).symm

/-- 概要：可逆な写像円柱の関手は存在する全ての小さい余極限を保つ。
方針：左右の評価と円柱の余極限保存を点ごとの pushout で貼る。
規約：形 J の余極限が単体集合で存在することだけを要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと骨格の余極限。 -/
instance equivalenceMappingCylinderFunctor_preservesColimitsOfShape
    (J : Type*) [Category* J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J equivalenceMappingCylinderFunctor.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J equivalenceMappingCylinderZeroNat
    equivalenceMappingCylinderArrowNat equivalenceMappingCylinderInlNat
    equivalenceMappingCylinderInrNat (fun f ↦ IsPushout.of_hasPushout _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
