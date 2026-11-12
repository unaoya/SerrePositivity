module

public import SerrePositivity.KST.Spectra.RelativeTriangleContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance

/-!
概要：相対三角形から Kan 複体への点つき写像空間の成分は一つである。
方針：基点固定の実際の収縮を π₀ に適用する。
規約：選択した基点は零写像。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの三角形の交換の式を全成分で計算する。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：相対三角形の Kan 値の写像空間の π₀ は一元集合。
方針：恒等射と零射の収縮から各成分が同じ零写像の成分と一致することを得る。
規約：源の相対三角形を Kan 置換する必要はない。
使われ方：Goerss–Jardine I §7。自己 pullback へ向かう連結射の全射性への適用。 -/
instance triangleDiskHom_piZero_subsingleton (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : Subsingleton (π₀ (PointedObject.basedHom triangleDisk.{u} Y).right) := by
  let A := PointedObject.basedHom triangleDisk.{u} Y
  obtain ⟨H, _⟩ := triangleDiskHom_exists_contraction Y
  refine ⟨?_⟩
  intro a b
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨w, rfl⟩ := π₀.mk_surjective b
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapPiZero_eq_of_homotopy H (π₀.mk v)
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapPiZero_eq_of_homotopy H (π₀.mk w)
  simp only [mapπ₀_mk] at hv hw
  exact hv.trans hw.symm

end

end SerrePositivity.KST.Spectra
