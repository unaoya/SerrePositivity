module

public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyComponents

/-!
概要：全基点 π_* 同型への後合成は点つき射の成分の等式を反映する。
方針：内部 Hom の標的変数での同型性を π₀ の単射性として使う。
規約：始域の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。選んだ比較の自然性の打ち消し。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全基点 π_* 同型への合成が同じ成分なら元の射も同じ成分。
方針：内部 Hom の π₀ への後合成の単射性で打ち消す。
規約：二つの標的は Kan、始域は任意。
使われ方：Goerss–Jardine I §7。BF 比較射を介した自然性の証明。 -/
theorem componentOf_cancel_post_piIsomorphism {A X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (p : X ⟶ Y)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p.right) (a b : A ⟶ X)
    (h : componentOf (a ≫ p) = componentOf (b ≫ p)) : componentOf a = componentOf b := by
  have hi := (post_piIsomorphism A p hp).piZero_bijective_at
    (PointedSimplicialSet.basepoint (PointedObject.basedHom A X))
  apply hi.injective
  simpa only [componentOf, mapπ₀_mk, familyVertex_post] using h

end

end SerrePositivity.KST.Spectra.PointedMapping
