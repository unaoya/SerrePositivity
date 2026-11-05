module

public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
概要：loop の正次数の群同型の標的自然性。
方針：全自然数次数の構成済みの自然性を正次数の通常の群の表示へ移す。
規約：次数 n は実際の n+1。
使われ方：Goerss–Jardine I §7、VIII §1。球面の Hom の係数の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop の正次数の群の次数移動は係数の点つき Kan 射に自然。
方針：全次数の集合の同値の自然性を同じ基礎写像の群同型へ適用する。
規約：両係数は Kan。
使われ方：Goerss–Jardine I §7、VIII §1。次数移動と係数の射の可換式。 -/
theorem loopPositiveHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : KanHomotopyGroup (loopSpace Y).right n (loopSpace Y).basepoint) :
    loopPositiveHomotopyEquiv Z n
        (pointedGroupMap (X := loopSpace Y) (Y := loopSpace Z) n
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := Y) (Z := Z) p) a) =
      pointedGroupMap (n + 1) p (loopPositiveHomotopyEquiv Y n a) := by
  have h := loopHomotopyEquiv_natural p (n + 1) a
  simpa only [loopHomotopyEquiv, _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy, _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map,
    pointedGroupMap, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using h

end

end SerrePositivity.KST.Spectra
