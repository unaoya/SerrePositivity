module
public import SerrePositivity.KST.SConstruction.ZeroRowKanLoopEquivalence
public import SerrePositivity.KST.SConstruction.PointedPiLocalized

/-! # 元の未置換の零行 loop 射の局所化同型
概要：正の反復の元の零行 loop 射は anodyne 局所化で可逆になる。
方針：零段基点を一つ取り、証明済みの Kan 延長の π 同型と厳密な単位の回収式を使う。
規約：元の零行の Kan 性は要求しない。使われ方：元の構造射の随伴への同型性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 元の零行 loop 射は、正の全反復で元の anodyne 局所化において可逆。 -/
lemma zeroRowLoopComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowLoopComparison (r + 1) X)) := by
  let b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌ :=
    Classical.arbitrary _
  let Q := AnodyneHomotopy.anodyneQ
  let i := PointedKanReplacement.unit.app (zeroRowPointedModel (r + 1) X b)
  let k := zeroRowKanLoopComparison (r + 1) X b
  have hi : IsIso (Q.map i.right) :=
    (Localization.inverts Q anodyneExtensions) _ (PointedKanReplacement.unit_anodyne _)
  have hk : IsIso (Q.map k.right) :=
    pointed_localized_isIso_of_piIsomorphism k (zeroRowKanLoopComparison_piIsomorphism r X b)
  have hf : i.right ≫ k.right = zeroRowLoopComparison (r + 1) X :=
    congrArg Under.Hom.right (zeroRowKanLoopComparison_unit (r + 1) X b)
  rw [← hf, Q.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
