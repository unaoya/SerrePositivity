module
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison

/-! # 元の局所化弱同値から同じ Ex∞ 点つき射の全基点 π 同型へ
概要：元の点つき射が anodyne 局所化で可逆なら、その実 Ex∞ 射は全基点 π 同型。
方針：同じ anodyne 単位と元の射の厳密自然性を使い、源単位を消去する。
規約：元の対象の Kan 性は不要。使われ方：新 BF 関手の境界 Kan 射の不変性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.SimplicialModel

/-- 元の同じ局所化弱同値の Ex∞ 点つき射は全基点 π 同型。 -/
lemma exInfinityPointedKanMap_piIsomorphism_of_localized
    {X Y : PointedSSetObject.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map
      (show X.obj ⟶ Y.obj from f).right)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (exInfinityPointedKanMap f).hom.right := by
  let Q := AnodyneHomotopy.anodyneQ
  let _ := hf
  let _ : IsIso (Q.map (exInfinityPointedUnit X).right) :=
    (Localization.inverts Q anodyneExtensions) _ (exInfinityPointedUnit_anodyne X)
  let _ : IsIso (Q.map (exInfinityPointedUnit Y).right) :=
    (Localization.inverts Q anodyneExtensions) _ (exInfinityPointedUnit_anodyne Y)
  have h : IsIso (Q.map (exInfinityPointedUnit X).right ≫
      Q.map (exInfinityPointedKanMap f).hom.right) := by
    rw [← Q.map_comp, ← Under.comp_right, exInfinityPointedUnit_naturality]
    change IsIso (Q.map ((show X.obj ⟶ Y.obj from f).right ≫
      (exInfinityPointedUnit Y).right))
    rw [Q.map_comp]
    infer_instance
  exact kanPiIsomorphism_of_localized_isIso _ ((isIso_comp_left_iff _ _).mp h)

end SerrePositivity.KST.SConstruction
