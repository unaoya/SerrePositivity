module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNativeOmega
public import SerrePositivity.KST.SConstruction.KSequenceMaps

/-! # 元の K の各段と全入力の native な Ω 比較
概要：零段を元の K 空間に保った列の全段を、実際の loop ∞ 関手への比較とともに与える。
方針：零段は次段の loop と全単体で一致し、正の段には元の全入力円柱を使う。
規約：元の Kan 列の対象・段の射を厳密に回収する。BF の単射置換の関手化は別工程。
使われ方：K の列の全入力 Ω 構造から、列の厳密化と単射置換への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の K の各 Kan 段を与える strict な点つき関手。 -/
def kKanSequenceLevelFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  match r with
  | 0 => boundaryKSpaceFunctor
  | r + 1 => boundaryKanRealizationFunctor r

/-- 段の関手の対象は元の K の Kan 列の対象そのもの。 -/
lemma kKanSequenceLevelFunctor_obj (r : ℕ) (X : StableModel.{u}) :
    (kKanSequenceLevelFunctor r).obj X = ((kKanSequence X).level r).space := by
  cases r <;> rfl

/-- 段の関手の射は列の厳密化へ既に渡している元の段の射そのもの。 -/
lemma kKanSequenceLevelFunctor_map (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (kKanSequenceLevelFunctor r).map f =
      eqToHom (kKanSequenceLevelFunctor_obj r X) ≫ kKanSequenceLevelMap f r ≫
        eqToHom (kKanSequenceLevelFunctor_obj r Y).symm := by
  cases r <;> simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;> rfl

/-- 元の段の関手の値は全て Kan。 -/
instance kKanSequenceLevelFunctor_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((kKanSequenceLevelFunctor r).obj X).right) := by
  cases r with
  | zero => exact boundaryKSpaceFunctor_kanComplex X
  | succ r => exact boundaryKanRealization_kanComplex r X

/-- 小さい通常の入力図式に対する、元の K の各段の全入力図式。 -/
def kKanCoherentLevelDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PointedKanInfinity.{u} :=
  pointedKanCoherentDiagram (F ⋙ kKanSequenceLevelFunctor r)
    (fun i => kKanSequenceLevelFunctor_kanComplex r (F.obj i))

/-- 正の段の全入力図式は元の反復 S の図式そのもの。 -/
lemma kKanCoherentLevelDiagram_succ {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) :
    kKanCoherentLevelDiagram F (r + 1) =
      pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)) := rfl

/-- 零段の全入力図式は、次段への実際の loop ∞ 関手の後合成に厳密に一致。 -/
lemma kKanCoherentLevelDiagram_zero {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) :
    kKanCoherentLevelDiagram F 0 =
      kKanCoherentLevelDiagram F 1 ≫ pointedKanLoopInfinity :=
  (boundaryKanLoopInfinity_diagram 0 F).symm

/-- 元の K の全段での、実際の loop ∞ 関手への図式全体の Ω 同型。 -/
def kKanNativeOmegaIso {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kKanCoherentLevelDiagram F r)
      (kKanCoherentLevelDiagram F (r + 1) ≫ pointedKanLoopInfinity) :=
  match r with
  | 0 => eqToIso (congrArg (fun p => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
      (kKanCoherentLevelDiagram_zero F))
  | r + 1 => boundaryAssemblyNativeOmegaIso r F

/-- 正の段の Ω 同型には、元の固定構造射を持つ指定した全入力変換を使う。 -/
lemma kKanNativeOmegaIso_succ {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) :
    kKanNativeOmegaIso F (r + 1) = boundaryAssemblyNativeOmegaIso r F := rfl

end SerrePositivity.KST.SConstruction
