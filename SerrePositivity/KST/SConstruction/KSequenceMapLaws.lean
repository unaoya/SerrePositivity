module
public import SerrePositivity.KST.SConstruction.MonicKSequenceMaps
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-! # K の候補列の射のホモトピー関手法則
概要：構成した列の射は各段の点つきホモトピー成分で恒等・合成を保つ。
方針：置換射影の後で元の関手法則を使い、射影のホモトピー逆で打ち消す。
規約：厳密な列の射の等号は主張しない。使われ方：K の関手性と選択独立性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping

/-- 概要：Kan な標的の π 同型への後合成は点つき射の成分を区別する。
方針：比較のホモトピー逆を後合成し、その合成を恒等射と比較する。
規約：源 A の Kan 性は不要。使われ方：置換射影の成分での打ち消し。 -/
lemma pointedComponent_cancel_right_of_piIsomorphism {A E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p.right) (a b : A ⟶ E)
    (h : componentOf (a ≫ p) = componentOf (b ≫ p)) : componentOf a = componentOf b := by
  obtain ⟨g, hleft, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse p hp
  have hi : componentOf (p ≫ g) = componentOf (𝟙 E) :=
    ((piZero_eq_iff_pointedHomotopy _ _).mpr hleft).symm
  calc
    componentOf a = componentOf ((a ≫ p) ≫ g) := by
      simpa only [Category.comp_id, Category.assoc] using componentOf_comp_left hi.symm a
    _ = componentOf ((b ≫ p) ≫ g) := componentOf_comp_right h g
    _ = componentOf b := by
      simpa only [Category.comp_id, Category.assoc] using componentOf_comp_left hi b

/-- 概要：未置換の候補列の各段の写像は恒等射を保つ。
方針：零段と正の段の関手の恒等法則。
規約：厳密等号。使われ方：置換後の恒等法則の比較。 -/
lemma kKanSequenceLevelMap_id (X : StableModel.{u}) (r : ℕ) :
    kKanSequenceLevelMap (𝟙 X) r = 𝟙 _ := by
  cases r with
  | zero => exact CategoryTheory.Functor.map_id _ X
  | succ r => exact CategoryTheory.Functor.map_id _ X

/-- 概要：未置換の候補列の各段の写像は合成を保つ。
方針：零段と正の段の関手の合成法則。
規約：厳密等号。使われ方：置換後の合成法則の比較。 -/
lemma kKanSequenceLevelMap_comp {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ) :
    kKanSequenceLevelMap (f ≫ g) r = kKanSequenceLevelMap f r ≫ kKanSequenceLevelMap g r := by
  cases r with
  | zero => exact CategoryTheory.Functor.map_comp _ f g
  | succ r => exact CategoryTheory.Functor.map_comp _ f g

/-- 概要：単射な K の候補列に構成した恒等入力の射は各段で恒等射と同じ成分。
方針：置換射影との合成を計算し、その π 同型を成分で打ち消す。
規約：全段で成立。使われ方：ホモトピー関手の恒等法則。 -/
lemma monicKKanSequenceMap_id_component (X : StableModel.{u}) (r : ℕ) :
    componentOf ((monicKKanSequenceMap (𝟙 X)).app r) =
      componentOf (𝟙 (((monicKKanSequence X).level r).space)) := by
  apply pointedComponent_cancel_right_of_piIsomorphism
    ((monicKKanSequenceProjection X).app r)
    (monicKKanSequenceProjection_piIsomorphism X r)
  simpa only [kKanSequenceLevelMap_id, Category.comp_id, Category.id_comp] using
    monicKKanSequenceMap_projection_component (𝟙 X) r

/-- 概要：単射な K の候補列に構成した合成入力の射は各段で射の合成と同じ成分。
方針：射影の後で二つの成分の比較と元の関手の合成法則を使い、射影を打ち消す。
規約：全段で成立。使われ方：ホモトピー関手の合成法則。 -/
lemma monicKKanSequenceMap_comp_component {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ) :
    componentOf ((monicKKanSequenceMap (f ≫ g)).app r) =
      componentOf ((monicKKanSequenceMap f).app r ≫ (monicKKanSequenceMap g).app r) := by
  apply pointedComponent_cancel_right_of_piIsomorphism
    ((monicKKanSequenceProjection Z).app r)
    (monicKKanSequenceProjection_piIsomorphism Z r)
  have hf := componentOf_comp_right (monicKKanSequenceMap_projection_component f r)
    (kKanSequenceLevelMap g r)
  have hg := componentOf_comp_left (monicKKanSequenceMap_projection_component g r)
    ((monicKKanSequenceMap f).app r)
  have hfg := monicKKanSequenceMap_projection_component (f ≫ g) r
  rw [kKanSequenceLevelMap_comp] at hfg
  simp only [Category.assoc] at hf hg ⊢
  exact hfg.trans (hf.symm.trans hg.symm)

end SerrePositivity.KST.SConstruction
