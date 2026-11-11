module
public import SerrePositivity.KST.SConstruction.KSequenceMapLaws
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-! # K の候補列の段ごとのホモトピー集合の関手
概要：置換列の射が誘導する全自然数次数の写像は厳密な関手法則を満たす。
方針：各段のホモトピー関手法則を L9 の基点固定ホモトピー不変性で写す。
規約：スペクトルの完成やその関手性の代用にはしない。使われ方：段ごとの π 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping

/-- 概要：同じ点つきホモトピー成分の射は全次数で同じ誘導写像を与える。
方針：成分の等式を実際の基点固定ホモトピーへ戻し、L9 の不変性を使う。
規約：零次数を含む。使われ方：成分での法則から誘導写像の法則への移送。 -/
lemma pointedHomotopyMap_eq_of_component {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] {f g : A ⟶ B}
    (h : componentOf f = componentOf g) (n : ℕ) :
    Spectra.pointedHomotopyMap n f = Spectra.pointedHomotopyMap n g := by
  obtain ⟨H, hH⟩ := (piZero_eq_iff_pointedHomotopy f g).mp h
  funext a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy f g H hH) a

/-- 概要：単射な K の候補列の各段の全次数ホモトピー集合の関手。
方針：実際に構成した列の射の誘導写像に、成分での恒等・合成法則を適用する。
規約：r と n を固定する。使われ方：反復 S の Kan 模型での自然な π の計算。 -/
def kStageHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (((monicKKanSequence X).level r).space).right n
    (((monicKKanSequence X).level r).space).basepoint
  map f := ↾(Spectra.pointedHomotopyMap n ((monicKKanSequenceMap f).app r))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((monicKKanSequenceMap (𝟙 X)).app r) a = a
    rw [pointedHomotopyMap_eq_of_component (monicKKanSequenceMap_id_component X r) n]
    exact Spectra.pointedHomotopyMap_id _ n a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((monicKKanSequenceMap (f ≫ g)).app r) a =
      Spectra.pointedHomotopyMap n ((monicKKanSequenceMap g).app r)
        (Spectra.pointedHomotopyMap n ((monicKKanSequenceMap f).app r) a)
    rw [pointedHomotopyMap_eq_of_component (monicKKanSequenceMap_comp_component f g r) n]
    exact Spectra.pointedHomotopyMap_comp n _ _ a

/-- 概要：未置換の反復 S の候補列の段ごとのホモトピー集合の関手。
方針：元の各段の関手が持つ恒等・合成法則に π の誘導写像を適用する。
規約：零段は既定の K 空間。使われ方：置換した列との自然な比較の標的。 -/
def rawKStageHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (((kKanSequence X).level r).space).right n
    (((kKanSequence X).level r).space).basepoint
  map f := ↾(Spectra.pointedHomotopyMap n (kKanSequenceLevelMap f r))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n (kKanSequenceLevelMap (𝟙 X) r) a = a
    rw [kKanSequenceLevelMap_id]
    exact Spectra.pointedHomotopyMap_id _ n a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n (kKanSequenceLevelMap (f ≫ g) r) a =
      Spectra.pointedHomotopyMap n (kKanSequenceLevelMap g r)
        (Spectra.pointedHomotopyMap n (kKanSequenceLevelMap f r) a)
    rw [kKanSequenceLevelMap_comp]
    exact Spectra.pointedHomotopyMap_comp n _ _ a

/-- 概要：単射置換した列の射影は各段・各次数のホモトピー集合の自然変換。
方針：射影との合成の成分の比較を、全次数の誘導写像の等式へ移す。
規約：零段・零次数も含む。使われ方：反復 S の π の自然な比較。 -/
def kStageHomotopyProjection (r n : ℕ) :
    kStageHomotopyFunctor r n ⟶ rawKStageHomotopyFunctor r n where
  app X := ↾(Spectra.pointedHomotopyMap n ((monicKKanSequenceProjection X).app r))
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((monicKKanSequenceProjection Y).app r)
        (Spectra.pointedHomotopyMap n ((monicKKanSequenceMap f).app r) a) =
      Spectra.pointedHomotopyMap n (kKanSequenceLevelMap f r)
        (Spectra.pointedHomotopyMap n ((monicKKanSequenceProjection X).app r) a)
    rw [← Spectra.pointedHomotopyMap_comp, ← Spectra.pointedHomotopyMap_comp]
    exact congrFun (pointedHomotopyMap_eq_of_component
      (monicKKanSequenceMap_projection_component f r) n) a

/-- 概要：置換射影のホモトピー集合への誘導写像は各入力で同型。
方針：射影の全基点 π 同型から得る実際の同値と誘導写像を照合する。
規約：零次数を含む。使われ方：段ごとの自然同型。 -/
instance kStageHomotopyProjection_app_isIso (r n : ℕ) (X : StableModel.{u}) :
    IsIso ((kStageHomotopyProjection r n).app X) := by
  let p := (monicKKanSequenceProjection X).app r
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism n p.right
    (monicKKanSequenceProjection_piIsomorphism X r) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  have he : (kStageHomotopyProjection r n).app X = e.toIso.hom := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply n p.right
      (monicKKanSequenceProjection_piIsomorphism X r)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) a).symm
  rw [he]
  infer_instance

/-- 概要：単射置換した列と元の反復 S の列は各段・各次数で自然に同じホモトピー集合を持つ。
方針：全入力で同型な射影の自然変換を自然同型へ束ねる。
規約：スペクトルの Ω 条件は使わない。使われ方：段ごとの π の模型独立性。 -/
def kStageHomotopyIso (r n : ℕ) : kStageHomotopyFunctor r n ≅ rawKStageHomotopyFunctor r n :=
  NatIso.ofComponents (fun X => asIso ((kStageHomotopyProjection r n).app X))
    (fun f => (kStageHomotopyProjection r n).naturality f)

end SerrePositivity.KST.SConstruction
