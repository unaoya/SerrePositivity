module
public import SerrePositivity.KST.SConstruction.PointedPiLocalized
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison

/-! # 前向き弱比較四角形による全基点 π 同型の移送
概要：元の射を保持する可換四角形で、両縦比較が弱同値なら上辺から下辺へ移送する。
方針：anodyne 局所化の同型を合成し、可逆な比較を消去する。
規約：全て Kan 対象。使われ方：実 BF 段の入力射の Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.SimplicialModel

/-- 同じ前向き弱比較と厳密な四角形は、元の下辺の全基点 π 同型を与える。 -/
lemma pointedPiIsomorphism_of_weakComparisonSquare
    {A B X Y : PointedSimplicialSet.{u}} [KanComplex A.right] [KanComplex B.right]
    [KanComplex X.right] [KanComplex Y.right]
    (a : A ⟶ B) (c : A ⟶ X) (d : B ⟶ Y) (f : X ⟶ Y)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) (hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right)
    (hd : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism d.right) (h : a ≫ d = c ≫ f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right := by
  let Q := AnodyneHomotopy.anodyneQ
  let _ : IsIso (Q.map a.right) := pointed_localized_isIso_of_piIsomorphism a ha
  let _ : IsIso (Q.map c.right) := pointed_localized_isIso_of_piIsomorphism c hc
  let _ : IsIso (Q.map d.right) := pointed_localized_isIso_of_piIsomorphism d hd
  have hi : IsIso (Q.map (a ≫ d).right) := by
    change IsIso (Q.map (a.right ≫ d.right))
    rw [Q.map_comp]
    infer_instance
  have hj : IsIso (Q.map c.right ≫ Q.map f.right) := by
    rw [← Q.map_comp, ← Under.comp_right, ← h]
    exact hi
  exact kanPiIsomorphism_of_localized_isIso f.right ((isIso_comp_left_iff _ _).mp hj)

end SerrePositivity.KST.SConstruction
