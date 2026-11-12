module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanCoefficientFibration

/-!
概要：係数図式の自然変換の可逆 path 置換を図式全体に自然に作る。
方針：各値の既存の path 置換を、pullback の普遍性で構造射について束ねる。
規約：可逆 path の始点が元の自然変換の像に等しく、終点は自由に動く。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の成分ごとの同値を自明 Kan fibration の span へ置換する。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}

/-- 概要：可逆な path の定値包含は単体集合の射について自然である。
方針：各次数で定値 path の係数の後合成を計算する。
規約：単体集合の充填性は要求しない。
使われ方：Kerodon 4.5.3（Tag 032Y） の図式の path 置換の標準切断の自然性。 -/
lemma equivalencePathRefl_postcomp {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc]
  change curry (snd (Δ[1] : SSet.{u}) X) ≫ (ihom (Δ[1] : SSet.{u})).map f =
    f ≫ curry (snd (Δ[1] : SSet.{u}) Y)
  rw [← curry_natural_right, ← curry_natural_left]
  apply congrArg curry
  exact (whiskerLeft_snd (Δ[1] : SSet.{u}) f).symm

/-- 概要：図式の構造射は成分の path 置換の間の射を誘導する。
方針：path の後合成と元の始域の構造射を pullback へ持ち上げる。
規約：係数図式の Kan 性は不要。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の図式の自然な置換。 -/
noncomputable def diagramPathReplacementMap (η : F ⟶ G) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (η.app i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (η.app j) :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj i) 0) (η.app i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap (G.map f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app i) ≫ F.map f) (by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc, pullback.condition,
        Category.assoc, ← η.naturality, ← Category.assoc])

/-- 概要：path 置換の構造射は path 座標では元の標的図式の構造射の後合成になる。
方針：pullback の持ち上げの第一射影を計算する。
規約：元の path はそのまま輸送する。
使われ方：Kerodon 4.8.4.1（Tag 01JX） の終点への射の自然性。 -/
lemma diagramPathReplacementMap_fst (η : F ⟶ G) {i j : I} (f : i ⟶ j) :
    diagramPathReplacementMap η f ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj j) 0) (η.app j) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj i) 0) (η.app i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap (G.map f) := pullback.lift_fst _ _ _

/-- 概要：path 置換の構造射は始域の座標では元の始域図式の構造射になる。
方針：pullback の持ち上げの第二射影を計算する。
規約：元の始域の座標を記憶する。
使われ方：Kerodon 4.8.4.1（Tag 01JX） の始域への射影の自然性。 -/
lemma diagramPathReplacementMap_snd (η : F ⟶ G) {i j : I} (f : i ⟶ j) :
    diagramPathReplacementMap η f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app i) ≫ F.map f := pullback.lift_snd _ _ _

/-- 概要：自然変換の各成分の可逆 path 置換は一つの単体集合値図式になる。
方針：pullback の二射影で恒等と合成の保存を検証する。
規約：元の図式と同じ小圏を添字とする。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の homotopy 極限の係数の同値不変性。 -/
noncomputable def diagramPathReplacement (η : F ⟶ G) : I ⥤ SSet.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (η.app i)
  map f := diagramPathReplacementMap η f
  map_id i := by
    apply pullback.hom_ext
    · rw [diagramPathReplacementMap_fst, G.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_id,
        Category.comp_id, Category.id_comp]
    · change diagramPathReplacementMap η (𝟙 i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app i) =
          (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (η.app i))) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app i)
      rw [diagramPathReplacementMap_snd, F.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply pullback.hom_ext
    · rw [diagramPathReplacementMap_fst, Category.assoc, diagramPathReplacementMap_fst,
        ← Category.assoc, diagramPathReplacementMap_fst, G.map_comp,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_comp, Category.assoc]
    · change diagramPathReplacementMap η (f ≫ g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection _ =
          (diagramPathReplacementMap η f ≫ diagramPathReplacementMap η g) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection _
      rw [diagramPathReplacementMap_snd, Category.assoc, diagramPathReplacementMap_snd,
        ← Category.assoc, diagramPathReplacementMap_snd, F.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
