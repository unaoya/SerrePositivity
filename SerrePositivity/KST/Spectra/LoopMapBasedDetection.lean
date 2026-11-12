module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationPointwiseComparison
public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyComponents
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsoSquareDetection

/-!
概要：標的の標準基点での正次数の同型性から、loop の全基点の同型性を得る。
方針：零次数は loop の次数移動、正次数は任意の loop の path fiber の五項比較を使う。
規約：標的や loop の連結性を仮定しない。使われ方：整数次数からの BF 同値検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

variable {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]

/-- path 全空間の射は、底の射の同値性を仮定せず全基点 π 同型。 -/
lemma basedPathMap_piIsomorphism (p : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (basedPathMap p).right := by
  let : KanComplex (terminal SSet.{u}) := by
    change Fibration (terminal.from (terminal SSet.{u}))
    have ht : terminal.from (terminal SSet.{u}) = 𝟙 (terminal SSet.{u}) := terminal.hom_ext _ _
    rw [ht]
    infer_instance
  have hY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (basedPathSpace_terminal_rlp Y)
  have hZ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (basedPathSpace_terminal_rlp Z)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := terminal.from (basedPathSpace Z).right) _ hZ
  have he : (basedPathMap p).right ≫ terminal.from (basedPathSpace Z).right =
      terminal.from (basedPathSpace Y).right := Subsingleton.elim _ _
  rw [he]
  exact hY

/-- 標準基点での正次数の同型性は、loop 全体の連結成分の全単射性を与える。 -/
lemma loopMap_piZero_bijective_of_positive (p : Y ⟶ Z)
    (hp : ∀ r, Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (r + 1) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p))) :
    Function.Bijective
      (mapπ₀ (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right) := by
  let f := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p
  let eY := loopHomotopyEquiv Y 0
  let eZ := loopHomotopyEquiv Z 0
  have he : eZ ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) ∘ eY := by
    funext a
    exact loopHomotopyEquiv_natural p 0 a
  have hb := (hp 0).comp eY.bijective
  rw [← he] at hb
  have hf := hb.of_comp_left eZ.injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero f.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)).1 hf

/-- path fiber の任意の頂点で、底の標準基点での正次数の同型性だけを使う。 -/
lemma pathFiberMap_positive_bijective_of_positive (p : Y ⟶ Z)
    (hp : ∀ r, Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (r + 1) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)))
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) _⦋0⦌) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (n + 1) (pathFiberMap p) (x := v) rfl) := by
  let qY := (pathEndpoint Y).right
  let qZ := (pathEndpoint Z).right
  let t := (basedPathMap p).right
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι qY (qY.app _ (basedPathSpace Y).basepoint)).app _ v
  have hc : qY ≫ p.right = t ≫ qZ :=
    (congrArg Under.Hom.right (pathEndpoint_natural p)).symm
  have hb : qY.app _ e = qY.app _ (basedPathSpace Y).basepoint :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base qY _ v
  have hb' : qZ.app _ (t.app _ e) = qZ.app _ (basedPathSpace Z).basepoint := by
    calc
      qZ.app _ (t.app _ e) = p.right.app _ (qY.app _ e) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq qY qZ t p.right hc e).symm
      _ = p.right.app _ (qY.app _ (basedPathSpace Y).basepoint) := congrArg _ hb
      _ = qZ.app _ (basedPathSpace Z).basepoint := pathFiberMap_base p
  have hg (r : ℕ) : Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (r + 1) p.right (x := qY.app _ e) rfl) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr (r + 1) p.right
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p).symm
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) rfl (hp r)
    have hx : qY.app _ e = Y.basepoint := hb.trans (pathEndpoint_basepoint Y)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr (r + 1) p.right hx.symm
      (congrArg (p.right.app _) hx.symm) rfl rfl h
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapOver_positive_bijective_at qY qZ t p.right hc e
    (fun r => basedPathMap_piIsomorphism p e (r + 1)) hg
    _ hb _ hb' (pathFiberMap p) (pathFiberMap_ι p) v rfl n

/-- 標準基点での正次数の同型性は、loop の任意の頂点で正次数の同型性を与える。 -/
lemma loopMap_positive_bijective_of_positive (p : Y ⟶ Z)
    (hp : ∀ r, Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (r + 1) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)))
    (l : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right _⦋0⦌) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (n + 1)
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right (x := l) rfl) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.map_bijective_iff_of_iso_square
    (loopBasedPathFiberIso Y) (loopBasedPathFiberIso Z)
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (pathFiberMap p) (loopBasedPathFiberIso_natural p) l (n + 1)).2
      (pathFiberMap_positive_bijective_of_positive p hp _ n)

/-- loop 後合成の全基点・全次数の検出には、元の標準基点の正次数だけで十分。 -/
lemma loopMap_piIsomorphism_of_positive (p : Y ⟶ Z)
    (hp : ∀ r, Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (r + 1) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right := by
  intro l n
  cases n with
  | zero =>
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero _ (x := l) rfl).2
      (loopMap_piZero_bijective_of_positive p hp)
  | succ n => exact loopMap_positive_bijective_of_positive p hp l n

end SerrePositivity.KST.Spectra
