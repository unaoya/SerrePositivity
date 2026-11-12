module

public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：Ω スペクトルの隣接段の全自然数次数の比較の自然性。
方針：随伴構造射の可換正方形と loop の次数移動の自然性を使う。
規約：零次数も含む。
使われ方：BF 1978 §2、HA §1.4.2。整数次数群の任意段表示の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの随伴構造射。
方針：suspension と loop の随伴の Hom 同値を適用する。
規約：全基点の π_* 同型を対象の Ω 条件として持つ射。
使われ方：BF 1978 §2、HA §1.4.2。隣接比較の計算。 -/
def adjointStructure (X : OmegaSpectrum.{u}) (k : ℕ) :
    (X.level k).space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (k + 1)).space :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level k).space (X.level (k + 1)).space) (X.sigma k)

/-- 概要：スペクトルの厳密な射は随伴構造射とも可換。
方針：Kan 列の既証の随伴構造射の可換式を使う。
規約：後の射は loop の後合成。
使われ方：BF 1978 §2、HA §1.4.2。隣接段の比較の自然性。 -/
theorem adjointStructure_comm {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (k : ℕ) :
    f.app k ≫ adjointStructure Y k = adjointStructure X k ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (k + 1)) := by
  let ff : KanSequence.Hom X.toKanSequence Y.toKanSequence := ⟨f.app, f.comm⟩
  exact ff.adjoint_comm k

/-- 概要：隣接段の群同型を随伴構造射と loop の同値で計算する。
方針：零次数と正次数で場合分けして元の定義を展開する。
規約：n は実際の自然数次数。
使われ方：BF 1978 §2、HA §1.4.2。段の比較の全次数の計算式。 -/
theorem transition_formula (X : OmegaSpectrum.{u}) (k n : ℕ) (a : levelHomotopy X k n) :
    transition X k n a = loopHomotopyEquiv (X.level (k + 1)).space n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (adjointStructure X k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a) := by
  cases n with
  | zero =>
    change loopZeroHomotopyEquiv (X.level (k + 1)).space
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism 0 (adjointStructure X k).right
        (X.omega_condition k) _ a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply]
    rfl
  | succ n =>
    change loopPositiveHomotopyEquiv (X.level (k + 1)).space n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (adjointStructure X k).right
        (X.omega_condition k) _ a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
    rfl

/-- 概要：隣接段の全自然数次数の群同型はスペクトルの射に関して自然。
方針：随伴構造射の可換正方形をホモトピー類へ送り、loop の自然性を適用する。
規約：零次数の誘導写像は元の連結成分の写像である。
使われ方：BF 1978 §2、HA §1.4.2。段の選択と π_* の関手の整合性。 -/
theorem transition_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (k n : ℕ)
    (a : levelHomotopy X k n) :
    transition Y k n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (n + 1) (f.app (k + 1)).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (transition X k n a) := by
  rw [transition_formula, transition_formula]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_square (adjointStructure X k).right (adjointStructure Y k).right
    (f.app k).right
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (k + 1))).right
    (congrArg Under.Hom.right (adjointStructure_comm f k)).symm
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) n a]
  exact loopHomotopyEquiv_natural (f.app (k + 1)) n _

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
