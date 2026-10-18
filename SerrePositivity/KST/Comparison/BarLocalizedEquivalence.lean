module

public import SerrePositivity.KST.Comparison.BarTupleMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-!
# 単体的モノイドの bar の局所化不変性

概要：基礎単体集合の局所化可逆なモノイド射は、bar 分類空間の局所化可逆な射を誘導する。
方針：Segal 座標で各行を有限積として比較し、既存の二重単体集合の対角化の定理を使う。
規約：Segal 1974 Proposition 1.5 の Kan 模型への移行。homotopy pullback の保存は主張しない。
使われ方：元のモノイドの bar と Kan なモノイドの bar の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel
open scoped Simplicial

/--
概要：モノイド次数と nerve の次数を交換した bar の射。
方針：各次数の一対象圏の nerve の射を flip 関手で移す。
規約：各行が基礎単体集合の有限積となる方向を外側に置く。
使われ方：行ごとの局所化可逆性を対角化へ渡す。
-/
def monoidBarRowsMap {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) :
    (bisimplicialBar M).flip ⟶ (bisimplicialBar N).flip :=
  (flipFunctor _ _ _).map (Functor.whiskerRight f (MonCat.toCat ⋙ nerveFunctor))

/--
概要：bar の行の射は Segal 座標で有限積の射に一致する。
方針：隣接射のラベルへの準同型の作用を比較する。
規約：Segal 座標の準同型に関する自然性。
使われ方：bar の各行の局所化可逆性。
-/
@[reassoc] theorem monoidBarRowIso_naturality {M N : SimplicialObject MonCat.{u}}
    (f : M ⟶ N) (r : ℕ) :
    (monoidBarRowsMap f).app (op ⦋r⦌) ≫ (monoidBarRowIso N r).hom =
      (monoidBarRowIso M r).hom ≫ monoidTupleMap f r := rfl

/--
概要：基礎射が局所化可逆なら、bar の各行の射も局所化可逆である。
方針：Segal 座標の同型で有限積の射へ移す。
規約：Segal 1974 Proposition 1.5 の入力の模型の不変性。
使われ方：二重単体集合の対角化の定理の仮定。
-/
theorem monoidBarRowsMap_localized_isIso {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map (Functor.whiskerRight f (forget MonCat))))
    (r : SimplexCategoryᵒᵖ) : IsIso (AnodyneHomotopy.anodyneQ.map ((monoidBarRowsMap f).app r)) := by
  obtain ⟨r⟩ := r
  obtain ⟨r⟩ := r
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have := monoidTupleMap_localized_isIso f hf r
  have h := congrArg Q.map (monoidBarRowIso_naturality f r)
  rw [Q.map_comp, Q.map_comp] at h
  have hc : IsIso (Q.map ((monoidBarRowsMap f).app (op ⦋r⦌)) ≫ Q.map (monoidBarRowIso N r).hom) :=
    h.symm ▸ inferInstanceAs (IsIso (Q.map (monoidBarRowIso M r).hom ≫ Q.map (monoidTupleMap f r)))
  exact (isIso_comp_right_iff _ _).mp hc

/--
概要：bar の対角は二つの単体方向を交換した後の対角に同型である。
方針：対象で恒等写像を使い、二つの面作用の交換を自然性で確認する。
規約：既存の monoidBar と HA の diagonal の界面の比較。
使われ方：対角化の局所化不変性を既存の bar へ移す。
-/
def monoidBarDiagonalFlipIso (M : SimplicialObject MonCat.{u}) :
    monoidBar M ≅ SerrePositivity.BisimplicialModel.diagonal.obj (bisimplicialBar M).flip :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    exact ((bisimplicialBar M).map f).naturality f)

/--
概要：bar の対角の方向交換はモノイド射に関して自然である。
方針：各単体次数で同じ一対象圏の nerve の写像になることを使う。
規約：比較の同型の向き。
使われ方：局所化後の射の可逆性の輸送。
-/
@[reassoc] theorem monoidBarDiagonalFlipIso_naturality {M N : SimplicialObject MonCat.{u}}
    (f : M ⟶ N) :
    monoidBarMap f ≫ (monoidBarDiagonalFlipIso N).hom =
      (monoidBarDiagonalFlipIso M).hom ≫
        SerrePositivity.BisimplicialModel.diagonal.map (monoidBarRowsMap f) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/--
概要：基礎単体集合で局所化可逆なモノイド射は、bar 分類空間でも局所化可逆である。
方針：各行の有限積座標の比較を、既存の対角化の局所化可逆性の定理へ適用する。
規約：Segal 1974 Proposition 1.5 の Kan 模型への移行。群状性はこの補題には不要。
使われ方：群状モノイドの Kan 置換の bar 比較。
-/
theorem monoidBarMap_localized_isIso {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map (Functor.whiskerRight f (forget MonCat)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidBarMap f)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have := SerrePositivity.BisimplicialModel.localized_diagonal_map (monoidBarRowsMap f)
    (monoidBarRowsMap_localized_isIso f hf)
  have h := congrArg Q.map (monoidBarDiagonalFlipIso_naturality f)
  rw [Q.map_comp, Q.map_comp] at h
  have hc : IsIso (Q.map (monoidBarMap f) ≫ Q.map (monoidBarDiagonalFlipIso N).hom) :=
    h.symm ▸ inferInstanceAs (IsIso (Q.map (monoidBarDiagonalFlipIso M).hom ≫
      Q.map (SerrePositivity.BisimplicialModel.diagonal.map (monoidBarRowsMap f))))
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Comparison
