module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.DiagramPathReplacement

/-!
概要：図式の自然な path 置換から両端への span と標準切断を構成する。
方針：各成分の既存の射影・終点射・切断を、構造射との可換性で束ねる。
規約：同値性の前提はデータの定義に要求しない。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の成分ごとの同値の自然な span 表示。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}

/-- 概要：図式の path 置換から元の始域への自然な射影。
方針：各成分の pullback の第二射影を束ねる。
規約：この射影は標的図式が局所 quasicategory なら成分ごとに自明 Kan fibration。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の span の始域側。 -/
noncomputable def diagramPathProjection (η : F ⟶ G) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement η ⟶ F where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app i)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap_snd η f

/-- 概要：図式の path 置換の終点は元の標的への自然変換。
方針：path 座標の構造射と終点評価の可換性を使う。
規約：各成分の実際の終点評価を使う。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の span の標的側。 -/
noncomputable def diagramPathEndpoint (η : F ⟶ G) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement η ⟶ G where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (η.app i)
  naturality i j f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap η f ≫
        (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj j) 0) (η.app j) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj j) 1) =
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj i) 0) (η.app i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj i) 1) ≫ G.map f
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap_fst, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc]

/-- 概要：path 置換の標準切断は path 座標で元の射の像の定値 path になる。
方針：標準切断を定義する pullback の持ち上げの第一射影を計算する。
規約：元の射 f は任意。
使われ方：Kerodon 4.5.3（Tag 032Y） の標準切断の図式全体の自然性。 -/
lemma equivalencePathReplacementSection_fst {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f =
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y := pullback.lift_fst _ _ _

/-- 概要：元の始域の図式は定値 path によって path 置換の図式へ自然に写る。
方針：二つの pullback 座標で自然性を検証する。
規約：成分ごとに選んだ逆射を使わない自然な切断。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の元の自然変換の復元。 -/
noncomputable def diagramPathSection (η : F ⟶ G) : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement η where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app i)
  naturality i j f := by
    apply pullback.hom_ext
    · change (F.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app j)) ≫
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj j) 0) (η.app j) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap η f) ≫
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj j) 0) (η.app j)
      calc
        _ = (F.map f ≫ η.app j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl (G.obj j) := by
          rw [Category.assoc, equivalencePathReplacementSection_fst, ← Category.assoc]
        _ = (η.app i ≫ G.map f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl (G.obj j) :=
          congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl (G.obj j)) (η.naturality f)
        _ = (η.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl (G.obj i)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap (G.map f) := by
          simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_postcomp]
        _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app i) ≫
            pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (G.obj i) 0) (η.app i)) ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap (G.map f) :=
          congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap (G.map f))
            (equivalencePathReplacementSection_fst (η.app i)).symm
        _ = _ := by rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap_fst]
    · change F.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app j) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app j) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection (η.app i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap η f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app j)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.comp_id, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacementMap_snd, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.id_comp]

/-- 概要：path 置換の切断と始域への射影の合成は元の図式の恒等変換。
方針：各成分の標準切断の厳密な逆関係を使う。
規約：図式全体の厳密な等式。
使われ方：Kerodon 4.8.4.1（Tag 01JX） の end の切断の同値性の二対三判定。 -/
lemma diagramPathSection_projection (η : F ⟶ G) :
    diagramPathSection η ≫ diagramPathProjection η = 𝟙 F := by
  apply NatTrans.ext
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection (η.app i)

/-- 概要：path 置換の切断と終点射の合成は元の自然変換である。
方針：定値 path の終点が元の射に等しいことを各成分で使う。
規約：実際の自然変換の厳密な分解。
使われ方：Kerodon 4.8.4.1（Tag 01JX）、7.5.4.6（Tag 03BB） の元の係数比較の同値性。 -/
lemma diagramPathSection_endpoint (η : F ⟶ G) :
    diagramPathSection η ≫ diagramPathEndpoint η = η := by
  apply NatTrans.ext
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map (η.app i)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
