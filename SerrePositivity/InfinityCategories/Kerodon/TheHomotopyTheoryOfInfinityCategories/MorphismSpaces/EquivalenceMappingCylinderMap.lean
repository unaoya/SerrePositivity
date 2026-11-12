module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjointPullback
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：可逆な写像円柱の可換正方形への関手性と端点の逆像。
方針：円柱上の直積の射と終域の射を pushout で貼る。
規約：比較射を変更せず単射へ自然に置換する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限のセル分解。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：可換正方形は可逆な写像円柱の射を誘導する。
方針：始域の円柱の射と終域の射を貼り合わせる。
規約：a は始域の射、b は終域の射。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の比較射の置換。 -/
noncomputable def equivalenceMappingCylinderMap {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder f' :=
  pushout.desc ((a ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ pushout.inl _ _) (b ≫ pushout.inr _ _)
    (by rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc,
      pushout.condition, ← Category.assoc, ← h, Category.assoc])

/-- 概要：写像円柱の誘導射は円柱上で指定された直積の射に一致する。
方針：pushout の desc の計算。
規約：零端を貼り合わせる。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然性。 -/
lemma equivalenceMappingCylinderMap_inl {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false) f ≫
      equivalenceMappingCylinderMap f f' a b h =
        (a ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ pushout.inl _ _ := pushout.inl_desc _ _ _

/-- 概要：写像円柱の誘導射は終域上で指定された射に一致する。
方針：pushout の desc の計算。
規約：終域は pushout の右包含で入る。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然性。 -/
lemma equivalenceMappingCylinderMap_inr {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false) f ≫
      equivalenceMappingCylinderMap f f' a b h = b ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

/-- 概要：写像円柱の誘導射は残った端点の包含と可換。
方針：円柱上の計算と端点の自然性を使う。
規約：残った端点は true。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然な単射。 -/
lemma equivalenceMappingCylinderIn_map {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f ≫ equivalenceMappingCylinderMap f f' a b h =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f' := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn, Category.assoc, equivalenceMappingCylinderMap_inl,
    ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc]
  rfl

/-- 概要：始域と終域の単射は写像円柱の単射を誘導する。
方針：零端の自然性の pullback 性を pushout の単射判定に適用する。
規約：元の射 f、f' の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの包含。 -/
instance equivalenceMappingCylinderMap_mono {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    [Mono a] [Mono b] : Mono (equivalenceMappingCylinderMap f f' a b h) := by
  have : Mono (a ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) := (tensorRight _).map_mono a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    a (a ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) b (equivalenceMappingCylinderMap f f' a b h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_equivalenceCylinderEndpoint_naturality a false) h
    (equivalenceMappingCylinderMap_inl f f' a b h) (equivalenceMappingCylinderMap_inr f f' a b h)

/-- 概要：写像円柱の残った端点の自然性の正方形は pullback。
方針：零端と一端が交わらないことから pushout 後の逆像を計算する。
規約：比較の射 a、b の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の相対セルの単射性。 -/
lemma equivalenceMappingCylinderIn_map_isPullback {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f) a (equivalenceMappingCylinderMap f f' a b h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_pushout_inl_comp_of_disjoint
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (a ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) b (equivalenceMappingCylinderMap f f' a b h)
    (equivalenceMappingCylinderMap_inl f f' a b h) (equivalenceMappingCylinderMap_inr f f' a b h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A' true) a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_equivalenceCylinderEndpoint_naturality a true)
  all_goals
    intro n x y he
    have hh := congrArg (fun s ↦ ((s.2.obj 0).as).down) he
    exact Bool.false_ne_true hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
