module
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositionTraces
public import SerrePositivity.KST.SConstruction.PointedCompatibilityInterchange

/-! # 元の K 合成補正と後続適合円柱の区間交換
概要：前の射の全補正区間と後ろの射の元の適合円柱を交換する実正方形列を構成する。
方針：両方の精密化パラメータを保持し、同じ補正列の suspension と元の K 適合円柱を合成する。
規約：元の全区間と適合円柱そのものを保持し、水平二面を明示的な二合成へ回収する。
使われ方：合成補正の射影 trace と構造適合面の二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 後続射の元の適合円柱を二本の精密化の共通パラメータへ制限する。 -/
def monicKPrismCompositeCompatibility (n : ℕ) :
    SSet.Homotopy
      (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g))
        (familyVertex ((kKanSequence (F.obj y)).sigma n ≫
          kKanSequenceLevelMap (F.map g) (n + 1))))
      (SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁
        kKanSequenceLevelMap (F.map g) n ≫ (kKanSequence (F.obj z)).sigma n))) := by
  let H := kKanOriginalPrismSpecifiedCompatibilityFamily n F g
  let j := snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g))
  exact
    { h := (j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by
        rw [SSet.ι₀_comp_assoc, H.h₀, SSet.comp_const]
        rfl
      h₁ := by
        rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]
        rfl
      rel := by
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        intro a
        exact False.elim a.1.property }

/-- 共通パラメータ上でも元の同じ適合円柱を全時刻で保持する。 -/
lemma monicKPrismCompositeCompatibility_h (n : ℕ) :
    (monicKPrismCompositeCompatibility F f g n).h =
      (snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ (kKanOriginalPrismSpecifiedCompatibilityFamily n F g).h := rfl

/-- 後続射の指定頂点では、元の同じ指定適合辺の実区間を回収する。 -/
lemma monicKPrismCompositeCompatibility_boundary (n : ℕ) :
    ((nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g)) ▷
      (Δ[1] : SSet.{u})) ≫ (monicKPrismCompositeCompatibility F f g n).h =
      (snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge n F g).edge := by
  rw [monicKPrismCompositeCompatibility_h, ← comp_whiskerRight_assoc]
  have h : (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g)) ≫
      snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (Δ[0] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [h, comp_whiskerRight_assoc, kKanOriginalPrismSpecifiedCompatibilityFamily_boundary]

/-- 元の前の補正列と後続適合円柱の全実交換正方形。 -/
def monicKPrismCompatibilityInterchangeSquares (n : ℕ) :=
  pointedCompatibilityInterchangeSquares
    (familyHomotopyChainPrecomp
      (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)))
      (monicKPrismTracedStage F f n).chain)
    ((kKanSequence (F.obj y)).sigma n ≫ kKanSequenceLevelMap (F.map g) (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n ≫
      (kKanSequence (F.obj z)).sigma n) (monicKPrismCompositeCompatibility F f g n)

/-- 元の前の補正全区間の suspension を指定した後続射で写した実 trace。 -/
def monicKPrismCompatibilityInterchangeTrace (n : ℕ)
    (d : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj y)).level n).space ⟶
      ((kKanSequence (F.obj z)).level (n + 1)).space) :
    List ((nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
        ((kKanSequence (F.obj z)).level (n + 1)).space).right) :=
  (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map (fun h =>
    (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷ (Δ[1] : SSet.{u})) ≫
      h ≫ (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj y)).level n).space).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space) d).right)

/-- 第二時刻の零面は、元の標的構造射と次段の後続射を使う全 trace。 -/
lemma monicKPrismCompatibilityInterchangeSquares_second_zero (n : ℕ) :
    (monicKPrismCompatibilityInterchangeSquares F f g n).map (SSet.ι₀ ≫ ·) =
      monicKPrismCompatibilityInterchangeTrace F f g n
        ((kKanSequence (F.obj y)).sigma n ≫ kKanSequenceLevelMap (F.map g) (n + 1)) := by
  simp only [monicKPrismCompatibilityInterchangeSquares,
    pointedCompatibilityInterchangeSquares_second_zero, familyHomotopyChainPrecomp_trace,
    List.map_map, Function.comp_def, monicKPrismCompatibilityInterchangeTrace, Category.assoc]

/-- 第二時刻の一面は、元の後続射の suspension と終域構造射を使う全 trace。 -/
lemma monicKPrismCompatibilityInterchangeSquares_second_one (n : ℕ) :
    (monicKPrismCompatibilityInterchangeSquares F f g n).map (SSet.ι₁ ≫ ·) =
      monicKPrismCompatibilityInterchangeTrace F f g n
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n ≫
          (kKanSequence (F.obj z)).sigma n) := by
  simp only [monicKPrismCompatibilityInterchangeSquares,
    pointedCompatibilityInterchangeSquares_second_one, familyHomotopyChainPrecomp_trace,
    List.map_map, Function.comp_def, monicKPrismCompatibilityInterchangeTrace, Category.assoc]

end SerrePositivity.KST.SConstruction
