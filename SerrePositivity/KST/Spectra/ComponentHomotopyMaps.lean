module

public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-!
概要：点つき写像空間で同じ成分の射は全次数で同じ誘導写像を与える。
方針：成分の等式を基点固定ホモトピーへ戻し、既存の相対ホモトピー不変性を使う。
規約：整数次数では各段の成分の等式を仮定する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の関手法則と自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同じ成分の点つき射は全自然数次数の誘導写像が一致する。
方針：成分を実際の基点固定ホモトピーとして表す。
規約：源と標的は Kan。
使われ方：Goerss–Jardine I §7。段ごとの比較射の選択の除去。 -/
theorem pointedHomotopyMap_eq_of_component {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] {f g : X ⟶ Y}
    (h : PointedMapping.componentOf f = PointedMapping.componentOf g) (n : ℕ) :
    pointedHomotopyMap n f = pointedHomotopyMap n g := by
  obtain ⟨H, hb⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy f g).mp h
  funext a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy f g H hb) a

/-- 概要：各段で同じ成分のスペクトルの射は全整数次数の誘導準同型が一致する。
方針：標準段でのホモトピー不変性を適用する。
規約：実際の二つの BF 射に対する主張。
使われ方：BF 1978 §2、HA §1.4.2。有理化の自然性。 -/
theorem OmegaSpectrum.homotopyMap_eq_of_levelComponent {X Y : OmegaSpectrum.{u}}
    (f g : X ⟶ Y)
    (h : ∀ n, PointedMapping.componentOf (f.app n) = PointedMapping.componentOf (g.app n))
    (j : ℤ) : homotopyMap f j = homotopyMap g j := by
  apply MonoidHom.ext
  intro a
  rw [homotopyMap_apply, homotopyMap_apply]
  exact congrFun (pointedHomotopyMap_eq_of_component (h _) _) a

end

end SerrePositivity.KST.Spectra
