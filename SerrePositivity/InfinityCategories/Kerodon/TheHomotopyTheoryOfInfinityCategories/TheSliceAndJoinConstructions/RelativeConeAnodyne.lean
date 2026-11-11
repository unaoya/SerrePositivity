module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanSingleFibrationRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：点の錐の相対的な貼り合わせは anodyne な部分複体の包含を anodyne にする。
方針：生成ホーンを join の標準単体のホーンへ移し、相対 coslice の fibration 性で一般化する。
規約：点の境界 ∂Δ[0] と anodyne な部分複体 B₀ → B の pushout-join を扱う。
使われ方：Kerodon 4.3.7（Tag 018P）、7.5.3.12（Tag 03B1） の重みの相対境界の錐による表示。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：点の境界と任意の正次元ホーンの pushout-join は anodyne。
方針：標準単体の join の同型で一つ高い次元のホーン包含へ移す。
規約：外側の最後のホーンも許す。
使われ方：Kerodon 4.3.7（Tag 018P）、7.5.3.12（Tag 03B1） の相対的な錐の延長。 -/
lemma joinUnion_pointBoundary_horn_anodyne (n : ℕ) (i : Fin (n + 2)) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary.{u} 0) (horn (n + 1) i)).ι := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.boundary_horn_preimage 0 n i]
  exact (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso
        (horn (0 + (n + 1) + 1) (Fin.cast (by omega) (i.natAdd (0 + 1))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 (n + 1)) (by rfl))).2
    (anodyneExtensions.horn_ι _)
/-- 概要：Kan fibration による点下の相対 coslice の射は Kan fibration。
方針：相対 coslice のホーンの持ち上げを点の境界とホーンの join の持ち上げへ移す。
規約：始域・終域の Kan 性は要求しない。
使われ方：Kerodon 4.3.7（Tag 018P）、7.5.3.12（Tag 03B1） の相対的な錐の延長。 -/
lemma relativePointSliceUnderMap_fibration {X Y : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [Fibration q] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceUnderMap p (boundary 0).ι q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceUnderMap_hasLiftingProperty (boundary 0) (horn (n + 1) i) q
  exact joinUnion_pointBoundary_horn_anodyne n i _
    ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
/-- 概要：点の境界と anodyne な部分複体の包含の pushout-join は anodyne。
方針：相対 coslice の射の fibration 性と与えた包含の全 fibration に対する持ち上げ性を使う。
規約：B₀ → B の anodyne 性を入力とし、点の境界は零次元に固定する。
使われ方：Kerodon 4.3.7（Tag 018P）、7.5.3.12（Tag 03B1） の相対的な錐の延長。 -/
lemma joinUnion_pointBoundary_anodyne {B : SSet.{u}} (B₀ : B.Subcomplex)
    (hB : anodyneExtensions B₀.ι) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary.{u} 0) B₀).ι := by
  intro X Y q hq
  have : Fibration q := ⟨hq⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_hasLiftingProperty_of_relativeSliceUnderMap
  intro p
  have := relativePointSliceUnderMap_fibration p q
  exact hB _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)

/-- 概要：anodyne な単射の像の包含から作る相対的な点の錐も anodyne。
方針：元の単射と像の包含を始域の同型で同定し、部分複体に対する相対錐の定理を使う。
規約：像を取る前の f の Mono 性と anodyne 性を要求する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の実際の重みの遷移から作る相対錐。 -/
lemma joinUnion_pointBoundary_range_anodyne {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : anodyneExtensions f) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary.{u} 0) (Subcomplex.range f)).ι := by
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : anodyneExtensions (Subcomplex.range f).ι :=
    (anodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (asIso (Subfunctor.toRange f)) (Iso.refl B) (by rfl))).1 hf
  exact joinUnion_pointBoundary_anodyne _ hR

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
