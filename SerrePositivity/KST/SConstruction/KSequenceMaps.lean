module
public import SerrePositivity.KST.SConstruction.KSpaceSequence
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturality
public import SerrePositivity.KST.Spectra.SequenceHomotopyRectification

/-! # 入力の射から作る K の Kan 列の比較
概要：各段の自然な射を、単射置換した源からの厳密な列の射へ修正する。
方針：構造射の成分での自然性と置換射影の可換式をつなぎ、L9 の厳密化を使う。
規約：Ω 条件は不要。使われ方：K の列の関手性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra.PointedMapping

/-- 概要：入力の射が与える K の候補列の各段の点つき射。
方針：零段は K 空間の関手、正の段は境界商の Kan 実現の関手で写す。
規約：構造射との比較は別に成分で示す。使われ方：列の射の厳密化の入力。 -/
def kKanSequenceLevelMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ∀ r, ((kKanSequence X).level r).space ⟶ ((kKanSequence Y).level r).space
  | 0 => boundaryKSpaceFunctor.map f
  | r + 1 => (boundaryKanRealizationFunctor r).map f

/-- 概要：K の各段の入力の射は構造射と成分で可換。
方針：零段は随伴の余単位の自然性、正の段は構成した suspension の自然性を使う。
規約：全段に適用。使われ方：L9 の列の射の厳密化の前提。 -/
lemma kKanSequenceLevelMap_comm {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap f r ≫
      (kKanSequence Y).sigma r) =
      componentOf ((kKanSequence X).sigma r ≫ kKanSequenceLevelMap f (r + 1)) := by
  cases r with
  | zero =>
    exact congrArg componentOf
      (pointedLoopCounit_naturality ((boundaryKanRealizationFunctor 0).map f))
  | succ r => exact boundaryKanAssemblySigma_naturality_component r f

/-- 概要：単射置換した源から、入力の射で与える各段の比較。
方針：源の置換射影に元の各段の写像を後合成する。
規約：標的は未置換の候補列。使われ方：厳密化の指定した成分。 -/
def monicKToRawLevelMap {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    ((monicKKanSequence X).level r).space ⟶ ((kKanSequence Y).level r).space :=
  (monicKKanSequenceProjection X).app r ≫ kKanSequenceLevelMap f r

/-- 概要：列の厳密な射の前合成は成分で可換な段の比較を保つ。
方針：構造射の可換式を使い、成分の等式の前合成を計算する。
規約：任意の Kan 列を使う一般形。使われ方：置換射影に沿う比較の移送。 -/
lemma pointedComponent_sequence_precompose {A B C : Spectra.KanSequence.{u}}
    (p : Spectra.KanSequence.Hom A B)
    (f : ∀ r, (B.level r).space ⟶ (C.level r).space)
    (hf : ∀ r, componentOf (PointedSimplicialSet.circle.{u} ◁ f r ≫ C.sigma r) =
      componentOf (B.sigma r ≫ f (r + 1))) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ (p.app r ≫ f r) ≫ C.sigma r) =
      componentOf (A.sigma r ≫ (p.app (r + 1) ≫ f (r + 1))) := by
  have h := componentOf_comp_left (hf r) (PointedSimplicialSet.circle.{u} ◁ p.app r)
  rw [whiskerLeft_comp, Category.assoc]
  calc
    _ = componentOf ((PointedSimplicialSet.circle.{u} ◁ p.app r ≫ B.sigma r) ≫
        f (r + 1)) := by simpa only [Category.assoc] using h
    _ = _ := by rw [p.comm r, Category.assoc]

/-- 概要：源を単射置換した各段の比較も構造射と成分で可換。
方針：元の成分の自然性の前に射影を suspension して合成し、厳密な射影の可換式を使う。
規約：全段に適用。使われ方：単射な源からの列の射の厳密化。 -/
lemma monicKToRawLevelMap_comm {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap f r ≫
      (kKanSequence Y).sigma r) =
      componentOf ((monicKKanSequence X).sigma r ≫ monicKToRawLevelMap f (r + 1)) :=
  pointedComponent_sequence_precompose (monicKKanSequenceProjection X)
    (kKanSequenceLevelMap f) (kKanSequenceLevelMap_comm f) r

/-- 概要：入力の射から得る単射置換した源からの厳密な Kan 列の射。
方針：成分で可換な各段の比較に L9 のホモトピー厳密化を適用する。
規約：各段は元の写像と同じ点つきホモトピー類。使われ方：K の関手性への接続。 -/
def monicKToRawMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (kKanSequence Y) :=
  Spectra.KanSequence.rectify (monicKKanSequence_sigma_mono X)
    (monicKToRawLevelMap f) (monicKToRawLevelMap_comm f)

/-- 概要：厳密化した列の射の各段は指定した写像の成分を保つ。
方針：L9 の逐次的な厳密化の成分の保持を使う。
規約：全段の点つき写像空間の成分。使われ方：実際の各段の射の比較。 -/
lemma monicKToRawMap_component {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf ((monicKToRawMap f).app r) = componentOf (monicKToRawLevelMap f r) :=
  Spectra.KanSequence.rectify_component _ _ _ r

end SerrePositivity.KST.SConstruction
