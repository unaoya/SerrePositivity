module

public import SerrePositivity.KST.Comparison.TensorSubcomplexTop

/-!
# 積の右因子に沿った四角形の制限

概要：積の右因子の写像に沿って四角形を制限し、同型なら比較を保存・反映する。
方針：積の厳密な引き戻しと四頂点の同型不変性を使う。
規約：Segal 1974 Proposition 1.6 の面の表示の移送。
使われ方：標準単体による面の表示へ境界の四角形を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel

/--
概要：積の右因子の写像に沿った四角形の制限。
方針：二因子の積の引き戻しの四角形を横に貼り合わせる。
規約：右因子の写像は任意。
使われ方：面の表示による四角形の比較。
-/
theorem tensorRestrictionSquare {X' X K L T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) (t : L ⟶ K) :
    CommSq ((X' ◁ t) ≫ a) (f ▷ L) p ((X ◁ t) ≫ b) :=
  (cartesianTensorSquare_isPullback f t).toCommSq.horiz_comp sq

/--
概要：右因子の同型に沿う制限はホモトピー引き戻し性を保存・反映する。
方針：四頂点のうち積の二頂点を同型で比較する。
規約：固定射や右因子の Kan 性は不要。
使われ方：標準単体と面の同型を通じた比較。
-/
theorem tensorRestriction_homotopyPullback_iff
    {X' X K L T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) (t : L ⟶ K) [IsIso t] :
    IsHomotopyPullback (tensorRestrictionSquare sq t) ↔ IsHomotopyPullback sq := by
  apply isHomotopyPullback_iff_of_localized_isIso (tensorRestrictionSquare sq t) sq
    (X' ◁ t) (𝟙 T') (X ◁ t) (𝟙 T) (by simp) ?_ (by simp) (by simp)
    (inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map ((tensorLeft X').map t))))
    (by infer_instance)
    (inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map ((tensorLeft X).map t))))
    (by infer_instance)
  exact (cartesianTensorSquare_isPullback f t).w.symm

end SerrePositivity.KST.Comparison
