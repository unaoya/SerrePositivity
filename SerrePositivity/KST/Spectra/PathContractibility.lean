module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedPathContractibility

public import SerrePositivity.KST.Spectra.PathContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyConstant

/-!
概要：基点に始まる path space のホモトピー群の自明性。
方針：区間の収縮から基点固定ホモトピーを作り、ホモトピー不変性を適用する。
規約：定数 path を基点とし零次数も扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動の長完全列。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：path space の収縮は定数 path の基点を固定する相対ホモトピー。
方針：基点生成部分複体の包含を定数射と同定し、収縮の基点固定式を使う。
規約：時刻零が定数射、時刻一が恒等射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。ホモトピー群の収縮。 -/
def pathContraction_basedHomotopy (Y : PointedSimplicialSet.{u}) :
    (RelativeMorphism.const : RelativeMorphism
      (.ofSimplex (basedPathSpace Y).basepoint) (.ofSimplex (basedPathSpace Y).basepoint)
        (SSet.const ⟨(basedPathSpace Y).basepoint,
          Subcomplex.mem_ofSimplex_obj (basedPathSpace Y).basepoint⟩)).Homotopy
      (RelativeMorphism.ofSimplex₀ (𝟙 (basedPathSpace Y).right)
        (basedPathSpace Y).basepoint (basedPathSpace Y).basepoint rfl) where
  h := pathContraction Y
  h₀ := (pathContraction_zero Y).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const _ _)
  h₁ := pathContraction_one Y
  rel := by
    rw [Subcomplex.ofSimplex_ι, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (basedPathSpace Y),
      comp_whiskerRight_assoc, pathContraction_constant, comp_toUnit_assoc]
    simp only [comp_toUnit_assoc]

/-- 概要：基点に始まる path space の全ホモトピー類は基点と一致する。
方針：基点固定収縮と定数射・恒等射の誘導写像を比較する。
規約：標的 Y は Kan。零次数を含む。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。 -/
theorem basedPathSpace_homotopy_eq_point (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (basedPathSpace Y).right n (basedPathSpace Y).basepoint) :
    a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  have hc : (SSet.const (X := (basedPathSpace Y).right) (basedPathSpace Y).basepoint).app _
      (basedPathSpace Y).basepoint = (basedPathSpace Y).basepoint := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (basedPathSpace Y)]
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n hc rfl (pathContraction_basedHomotopy Y) a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id] at h
  exact h.symm

/-- 概要：基点に始まる path space の全次数のホモトピー類は一元集合。
方針：全要素が基点と一致することを使う。
規約：零次数を含む。定数 path を基点とする。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。長完全列の全空間の項の消去。 -/
instance basedPathSpace_homotopy_subsingleton (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (basedPathSpace Y).right n (basedPathSpace Y).basepoint) where
  allEq a b := (basedPathSpace_homotopy_eq_point Y n a).trans
    (basedPathSpace_homotopy_eq_point Y n b).symm

end

end SerrePositivity.KST.Spectra
