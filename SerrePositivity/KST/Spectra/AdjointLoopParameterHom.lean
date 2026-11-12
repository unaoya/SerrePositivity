module

public import SerrePositivity.KST.Spectra.AdjointLoopKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceMappingExchange

/-!
概要：補助 loop 列の作用と単位の自然性を任意の全パラメータ族に拡張する。
方針：内部 Hom のパラメータ交換と元の構造随伴の厳密可換性を使う。
規約：nativeLoop との円交換因子の直接比較は行わない。
使われ方：相対 BF 右射影を含む全 Hom 自然性の実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 概要：補助 loop と任意の mapping パラメータの交換は厳密な列射。
方針：構造随伴の定義と交換の標的自然性・逆順交換を使う。
規約：パラメータの Kan 性や有限性を仮定しない。
使われ方：元の全パラメータ族への補助 loop の作用。 -/
def adjointLoopMappingExchange (A : PointedSimplicialSet.{u}) (X : KanSequence.{u}) :
    Hom (adjointLoop (mapping A X)) (mapping A (adjointLoop X)) :=
  Hom.ofAdjoint
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
      (X.level n).space).hom) (fun n ↦ by
      have hm (Y : KanSequence.{u}) : ordinaryStructureAdjoint (mapping A Y) n =
        (ihom A).map (ordinaryStructureAdjoint Y n) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u}
            (Y.level (n + 1)).space).hom := mapping_adjoint A Y n
      change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
          (X.level n).space).hom ≫ ordinaryStructureAdjoint (mapping A (adjointLoop X)) n =
        ordinaryStructureAdjoint (adjointLoop (mapping A X)) n ≫
          (ihom PointedSimplicialSet.circle.{u}).map
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
              (X.level (n + 1)).space).hom
      rw [hm, adjointLoop_ordinaryStructureAdjoint,
        adjointLoop_ordinaryStructureAdjoint, hm]
      change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
          (X.level n).space).hom ≫
        ((ihom A).map ((ihom PointedSimplicialSet.circle.{u}).map
            (ordinaryStructureAdjoint X n)) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u}
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space)).hom) =
        (ihom PointedSimplicialSet.circle.{u}).map
          ((ihom A).map (ordinaryStructureAdjoint X n) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u}
              (X.level (n + 1)).space).hom) ≫
          (ihom PointedSimplicialSet.circle.{u}).map
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
              (X.level (n + 1)).space).hom
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post_assoc PointedSimplicialSet.circle.{u} A
        (ordinaryStructureAdjoint X n)]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv A PointedSimplicialSet.circle.{u}]
      simp only [Iso.hom_inv_id, Category.comp_id]
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id])

/-- 概要：補助 loop は元の列射の全パラメータ族を同じパラメータの族へ写す。
方針：元の列射へ補助 loop を施し、パラメータを交換する。
規約：各段の射と構造可換性を厳密に保持する。
使われ方：相対 BF 右射影の全 Hom 可換条件。 -/
def adjointLoopParameterHom {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (f : Hom X (mapping A Y)) : Hom (adjointLoop X) (mapping A (adjointLoop Y)) :=
  (adjointLoopMap f).comp (adjointLoopMappingExchange A Y)

/-- 概要：全パラメータ作用の各段は元の射への loop と同じパラメータ交換。
方針：合成した列射の定義を取り出す。
規約：新しい各段の持ち上げを選ばない。
使われ方：元の単位と右射影の境界照合。 -/
lemma adjointLoopParameterHom_app {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (f : Hom X (mapping A Y)) (n : ℕ) :
    (adjointLoopParameterHom f).app n =
      (ihom PointedSimplicialSet.circle.{u}).map (f.app n) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A (Y.level n).space).hom := rfl

/-- 概要：補助 loop の全パラメータ作用は元の部分パラメータへの制限と可換。
方針：内部 Hom の標準交換の源自然性を各段へ適用する。
規約：パラメータの射に単射性を要求しない。
使われ方：全単体作用素を保つ全 Hom 比較。 -/
lemma adjointLoopParameterHom_pre {A B : PointedSimplicialSet.{u}} (i : B ⟶ A)
    {X Y : KanSequence.{u}} (f : Hom X (mapping A Y)) :
    adjointLoopParameterHom (f.comp (mappingPre i Y)) =
      (adjointLoopParameterHom f).comp (mappingPre i (adjointLoop Y)) := by
  apply Hom.ext_app
  intro n
  change (ihom PointedSimplicialSet.circle.{u}).map
      (f.app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} B (Y.level n).space).hom =
    ((ihom PointedSimplicialSet.circle.{u}).map (f.app n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A (Y.level n).space).hom) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i ((adjointLoop Y).level n).space
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right PointedSimplicialSet.circle.{u} i
    (Y.level n).space
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  erw [h]
  rw [Category.assoc]
  rfl

/-- 概要：元の補助単位は任意の全パラメータ族に対して厳密に自然。
方針：元の列射の随伴可換式のパラメータ交換を逆順交換で打ち消す。
規約：通常射・頂点・ホモトピー類の自然性に制限しない。
使われ方：同じ単位を回収する相対 BF 全 Hom 比較。 -/
lemma adjointLoopTailUnit_parameter_natural
    {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (f : Hom X (mapping A Y)) :
    f.comp (mappingPost A (adjointLoopTailUnit Y)) =
      (adjointLoopTailUnit X).comp
        (adjointLoopParameterHom (X := tail X) (Y := tail Y) (tailHom f)) := by
  apply Hom.ext_app
  intro n
  change f.app n ≫ (ihom A).map (ordinaryStructureAdjoint Y n) =
    ordinaryStructureAdjoint X n ≫
      ((ihom PointedSimplicialSet.circle.{u}).map (f.app (n + 1)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
          (Y.level (n + 1)).space).hom)
  have h := ordinaryStructureAdjoint_natural f n
  have hm := mapping_adjoint A Y n
  change ordinaryStructureAdjoint (mapping A Y) n = _ at hm
  rw [hm] at h
  have hh := congrArg (· ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A
      (Y.level (n + 1)).space).hom) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv A PointedSimplicialSet.circle.{u}] at hh
  simpa only [ordinaryStructureAdjoint, Category.assoc, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, Category.comp_id] using hh

end SerrePositivity.KST.Spectra.KanSequence
