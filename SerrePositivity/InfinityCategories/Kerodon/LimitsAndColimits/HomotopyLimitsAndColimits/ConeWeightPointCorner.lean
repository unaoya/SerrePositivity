module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanSingleFibrationRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveInitialComparison

/-!
概要：定値の一点重みから補助重みへの包含の cospan の相対境界は anodyne。
方針：補助重みの単射に沿う遷移を始対象を保つ単射として扱い、点側の pushout の同型で移す。
規約：添字の射の Mono 性と図式の脚の Fibration 性は別の条件として扱う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚だけが fibration の図式の一点側の重みの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：始対象の付加は対象上で単射な忠実関手の nerve の単射性を保つ。
方針：射を元の射と始対象からの一意な射に分け、対象と射の単射性を確認する。
規約：F の忠実性と対象上の単射性を前提とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の補助重みの一点側の比較。 -/
lemma withInitialMap_nerve_mono (F : C ⥤ D) [F.Faithful] (hF : Function.Injective F.obj) :
    Mono (nerveMap (WithInitial.map F)) := by
  have : (WithInitial.map F).Faithful :=
    { map_injective := fun {X Y} f g h => by
        cases X <;> cases Y
        · exact F.map_injective h
        · exact PEmpty.elim f
        · exact Subsingleton.elim _ _
        · exact Subsingleton.elim _ _ }
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful (WithInitial.map F)
  intro X Y h
  cases X <;> cases Y
  · exact congrArg WithInitial.of (hF (WithInitial.of.inj h))
  · cases h
  · cases h
  · rfl
/-- 概要：添字圏の単射に沿う補助重みの遷移は単射。
方針：over 圏の後合成の単射性と忠実性を始対象の付加後に nerve へ移す。
規約：添字圏の射 f の Mono 性を明示する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の補助重みの一点側の比較。 -/
lemma bousfieldKanConeWeight_map_mono {x y : C} (f : x ⟶ y) [Mono f] :
    Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight C).map f) := by
  have : (Over.map f).Faithful :=
    { map_injective := fun {a b} g h e => by
        apply Over.OverMorphism.ext
        exact congrArg (fun k : (Over.map f).obj a ⟶ (Over.map f).obj b => k.left) e }
  exact withInitialMap_nerve_mono (Over.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.overMap_obj_injective f)
/-- 概要：添字圏の単射に沿う補助重みの遷移は anodyne。
方針：両側の新しい始対象を保つ nerve の単射の left anodyne 性を使う。
規約：図式の値に Kan 性や fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の補助重みの一点側の比較。 -/
lemma bousfieldKanConeWeight_map_anodyne {x y : C} (f : x ⟶ y) [Mono f] :
    anodyneExtensions ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight C).map f) := by
  have : Mono (nerveMap (WithInitial.map (Over.map f))) :=
    bousfieldKanConeWeight_map_mono f
  intro E B p hp
  have : Fibration p := ⟨hp⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingInitial_leftAnodyne (WithInitial.map (Over.map f))
    (WithInitial.starInitial (C := Over x)) (WithInitial.starInitial (C := Over y)))
      p _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem
/-- 概要：始域の右脚が同型なら中央の相対境界の anodyne 性は終域の右脚から得られる。
方針：pushout の右包含の同型性から相対境界を右脚と同型の合成で表す。
規約：終域の右脚の anodyne 性を入力とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の補助重みの一点側の比較。 -/
lemma cospanRightCorner_anodyne_of_sourceRightIso {A B : WalkingCospan ⥤ SSet.{u}}
    (j : A ⟶ B) [IsIso (A.map WalkingCospan.Hom.inr)]
    (hB : anodyneExtensions (B.map WalkingCospan.Hom.inr)) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap j) := by
  let i := pushout.inr (A.map WalkingCospan.Hom.inr) (j.app .right)
  have : IsIso i := (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso
  have hk : i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap j = B.map WalkingCospan.Hom.inr :=
    pushout.inr_desc _ _ _
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap j = inv i ≫ B.map WalkingCospan.Hom.inr := by
    rw [← hk, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [he]
  exact anodyneExtensions.comp_mem (inv i) _ (MorphismProperty.of_isIso _ _) hB
/-- 概要：一点重みから補助重みへの包含の中央の相対境界は anodyne。
方針：定値一点の右脚の同型性と補助重みの右脚の anodyne 性を組み合わせる。
規約：AsSmall に持ち上げた cospan の実際の標準重みを扱う。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の補助重みの一点側の比較。 -/
lemma bousfieldKanConeWeightPoint_cospan_corner_anodyne : anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap
    (Functor.whiskerLeft AsSmall.up
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightPoint (I := AsSmall.{u} WalkingCospan)))) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have : IsIso ((AsSmall.up ⋙
      (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})).map
        WalkingCospan.Hom.inr) := inferInstanceAs (IsIso (𝟙 (Δ[0] : SSet.{u})))
  apply cospanRightCorner_anodyne_of_sourceRightIso
  exact bousfieldKanConeWeight_map_anodyne (AsSmall.up.map WalkingCospan.Hom.inr)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
