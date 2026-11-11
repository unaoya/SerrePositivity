module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedPointedHomotopy
public import SerrePositivity.KST.Spectra.PathContractibility
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
概要：点つき対象の基点を固定するホモトピーの相対表示。
方針：基点生成部分複体の包含を定数射と同定する。
規約：ホモトピーは全区間で基点を固定する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。置換と整数次数の不変性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき Kan 複体の射による全自然数次数の誘導写像。
方針：点つき射の基点保存を通常の誘導写像へ渡す。
規約：零次数では集合の写像。
使われ方：Goerss–Jardine I §7。置換のホモトピー逆の計算。 -/
def pointedHomotopyMap {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X.right n X.basepoint → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y.right n Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)

/-- 概要：点つき誘導写像は恒等射を保つ。
方針：通常のホモトピー類の恒等法則を使う。
規約：全自然数次数。
使われ方：Goerss–Jardine I §7。置換比較の逆の計算。 -/
@[simp]
theorem pointedHomotopyMap_id (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X.right n X.basepoint) :
    pointedHomotopyMap n (𝟙 X) a = a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id n a

/-- 概要：点つき誘導写像は合成を保つ。
方針：基点保存の証明の一意性と通常の合成法則を使う。
規約：全自然数次数。
使われ方：Goerss–Jardine I §7。置換のホモトピー逆の照合。 -/
theorem pointedHomotopyMap_comp {X Y Z : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] [KanComplex Z.right]
    (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X.right n X.basepoint) :
    pointedHomotopyMap n (f ≫ g) a = pointedHomotopyMap n g (pointedHomotopyMap n f a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f.right _ g.right _ _ a

/-- 概要：各段で基点固定ホモトピックなスペクトルの射は同じ整数次数の準同型を誘導する。
方針：標準段での全自然数次数のホモトピー不変性を使う。
規約：ホモトピーの族は実際の相対ホモトピーとして与える。
使われ方：BF 1978 §2、HA §1.4.2。置換のホモトピー比較。 -/
theorem OmegaSpectrum.homotopyMap_eq_of_levelHomotopy {X Y : OmegaSpectrum.{u}}
    (f g : X ⟶ Y)
    (H : ∀ k, (RelativeMorphism.ofSimplex₀ (f.app k).right
      (X.level k).space.basepoint (Y.level k).space.basepoint
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)).Homotopy
      (RelativeMorphism.ofSimplex₀ (g.app k).right
        (X.level k).space.basepoint (Y.level k).space.basepoint
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))) (j : ℤ) : homotopyMap f j = homotopyMap g j := by
  apply MonoidHom.ext
  intro a
  rw [homotopyMap_apply, homotopyMap_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy _ _ _ (H _) a

end

end SerrePositivity.KST.Spectra
