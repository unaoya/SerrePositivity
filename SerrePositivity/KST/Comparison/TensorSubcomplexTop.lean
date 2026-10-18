module

public import SerrePositivity.KST.Comparison.TensorSubcomplexGluing

/-!
# 全体の部分単体集合への制限と元の四角形

概要：右因子の全体の部分単体集合への制限は、元の四角形のホモトピー引き戻し性と同値である。
方針：全体の部分対象の包含の同型を四頂点の比較へ使う。
規約：Segal 1974 Proposition 1.6 の有限被覆の和が全体となる場合の復元。
使われ方：面の有限被覆から元の境界全体の四角形へ戻す。
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
概要：全体の部分単体集合への制限は元の四角形のホモトピー引き戻し性を保存・反映する。
方針：左右の固定因子との積で全体の部分対象の同型を使う。
規約：右因子の対象や固定射の Kan 性は不要。
使われ方：有限被覆の和が全体である場合の結論の復元。
-/
theorem tensorSubcomplex_homotopyPullback_top_iff
    {X' X K T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) :
    IsHomotopyPullback (tensorSubcomplexSquare sq ⊤) ↔ IsHomotopyPullback sq := by
  let : IsIso (⊤ : K.Subcomplex).ι :=
    inferInstanceAs (IsIso (SSet.Subcomplex.topIso K).hom)
  have hA : IsIso (AnodyneHomotopy.anodyneQ.map (X' ◁ (⊤ : K.Subcomplex).ι)) :=
    inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map
      ((tensorLeft X').map (SSet.Subcomplex.topIso K).hom)))
  have hY : IsIso (AnodyneHomotopy.anodyneQ.map (X ◁ (⊤ : K.Subcomplex).ι)) :=
    inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map
      ((tensorLeft X).map (SSet.Subcomplex.topIso K).hom)))
  apply isHomotopyPullback_iff_of_localized_isIso (tensorSubcomplexSquare sq ⊤) sq
    (X' ◁ (⊤ : K.Subcomplex).ι) (𝟙 T') (X ◁ (⊤ : K.Subcomplex).ι) (𝟙 T)
    (by simp) ?_ (by simp) (by simp) hA (by infer_instance) hY (by infer_instance)
  exact (cartesianTensorSquare_isPullback f (⊤ : K.Subcomplex).ι).w.symm

end SerrePositivity.KST.Comparison
