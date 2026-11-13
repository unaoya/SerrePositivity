module

public import SerrePositivity.KST.Spectra.StageComparisonNaturality
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence
public import SerrePositivity.KST.Spectra.LoopMapBasedDetection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：整数次数のホモトピー群の同型性を任意段の検出へ移す。
方針：次数 j = n - k を選び、任意段の表示の自然性で全単射性を移す。
規約：標準基点での条件と全基点の条件を区別する。使われ方：Sp の同値検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

local instance integerDetectionLoopKan (P : PointedSimplicialSet.{u}) [KanComplex P.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace P).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 全整数次数の群同型は、任意段の零次数を含む標準基点での全単射性を与える。 -/
lemma PiIsomorphism.levelMap_bijective {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y}
    (hf : PiIsomorphism f) (k n : ℕ) : Function.Bijective (levelMap f k n) := by
  let j : ℤ := (n : ℤ) - (k : ℤ)
  have hk : -j ≤ (k : ℤ) := by dsimp [j]; omega
  have hd : degree j k = n := by dsimp [degree, j]; omega
  have h := (homotopyMap_bijective_iff_levelMap f j k hk).1 (hf j)
  rwa [hd] at h

/-- 標準基点での整数次数の同型性と、任意段・全自然数次数の同型性は同値。 -/
lemma piIsomorphism_iff_levelMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    PiIsomorphism f ↔ ∀ k n, Function.Bijective (levelMap f k n) := by
  constructor
  · exact fun hf => hf.levelMap_bijective
  · intro hf j
    exact (homotopyMap_bijective_iff_levelMap f j (canonicalLevel j)
      (by have := canonicalLevel_admissible j; omega)).2 (hf _ _)

/-- 整数次数の同型は任意段の連結成分の全単射を与える。連結性は仮定しない。 -/
lemma PiIsomorphism.level_piZero_bijective {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y}
    (hf : PiIsomorphism f) (k : ℕ) : Function.Bijective (mapπ₀ (f.app k).right) := by
  let eX := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := (X.level k).space.right)
    (x := (X.level k).space.basepoint)
  let eY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := (Y.level k).space.right)
    (x := (Y.level k).space.basepoint)
  have he : eY ∘ levelMap f k 0 = mapπ₀ (f.app k).right ∘ eX := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a
  have hb := eY.bijective.comp (hf.levelMap_bijective k 0)
  rw [he] at hb
  exact (Function.Bijective.of_comp_iff _ eX.bijective).1 hb

/-- 全整数次数の標準群の同型性は、各段の任意の基点での π 同型性を与える。 -/
lemma PiIsomorphism.levelwise {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y}
    (hf : PiIsomorphism f) (k : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app k).right := by
  have hl := loopMap_piIsomorphism_of_positive (f.app (k + 1))
    (fun r => hf.levelMap_bijective (k + 1) (r + 1))
  have hc := (X.omega_condition k).comp hl
  have he := congrArg Under.Hom.right (adjointStructure_comm f k)
  change (f.app k).right ≫ (adjointStructure Y k).right =
    (adjointStructure X k).right ≫
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (k + 1))).right at he
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((adjointStructure X k).right ≫
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (k + 1))).right) at hc
  rw [← he] at hc
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hc (Y.omega_condition k)

/-- 整数次数の同型性と、各段の全基点の同型性は同値。連結性は不要。 -/
lemma piIsomorphism_iff_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    PiIsomorphism f ↔ ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app k).right :=
  ⟨fun hf => hf.levelwise, piIsomorphism_of_levelwise f⟩

local instance integerDetectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の BF 射の全整数次数の π 同型は、元の Sp の同じ辺の可逆性を検出する。 -/
theorem isInvertible_of_piIsomorphism {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : PiIsomorphism f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise f hf.levelwise

/-- 任意の Sp の一単体でも、同じ辺から回収した BF 射の整数次数の群で検出できる。 -/
theorem spEdge_isInvertible_of_piIsomorphism (s : Sp.{u} _⦋1⦌)
    (hs : PiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData s).2.2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) := by
  have h := isInvertible_of_piIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData s).2.2 hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_reconstruct s)).mp h

end SerrePositivity.KST.Spectra.OmegaSpectrum
