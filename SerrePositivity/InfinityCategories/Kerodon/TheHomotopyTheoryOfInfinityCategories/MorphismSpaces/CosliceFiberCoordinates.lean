module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：coslice 射影の fiber の全次数を端点と面の固定された単体として表示する。
方針：Δ[0] ⋆ Δ[n] の標準単体との同型を各次数で用いる。
規約：最初の頂点を x、残りの面を y に定値とする。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、Construction 5.5.2.1（Tag 01ZW）、coherent Hom との高次比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：点を前置した標準単体の join の標準単体表示。
方針：Core の点との join の標準同型を用いる。
規約：同型の始域は Δ[0] ⋆ Δ[n]。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左 pinched 単体の座標。 -/
def leftPointStdSimplexIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[n] ≅ Δ[n + 1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n

/-- 概要：点と標準単体の join の左包含は最初の頂点。
方針：join の頂点の公式を標準単体の定値射として読む。
規約：右因子の次数 n は任意。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左側の固定端点の確認。 -/
lemma joinStdSimplexIso_leftPoint_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (leftPointStdSimplexIso n).hom =
      stdSimplex.map (SimplexCategory.const _ _ 0) := by
  rw [leftPointStdSimplexIso, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso, Iso.trans_hom, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl_vertex]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso_hom_app_val]
  rfl

/-- 概要：点と標準単体の join の右包含は最初の頂点を除いた面。
方針：join の連結写像の右側の値は元の頂点番号に一を加えたもの。
規約：δ 0 が右因子の包含。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、fiber の底が定値である条件。 -/
lemma joinStdSimplexIso_leftPoint_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ (leftPointStdSimplexIso n).hom =
      stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n]).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_hom_app_val]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat 0 (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 0 0 PUnit.unit)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n (n + 1) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (by omega)]
  change 1 + i.val = ((0 : Fin (n + 2)).succAbove i).val
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  simp only [Fin.val_succ]
  omega

/-- 概要：coslice fiber の n 単体を元の (n+1) 単体として読む。
方針：join の同型の逆で前合成し、Yoneda の同値を適用する。
規約：固定端点は x、射影の値は y。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coherent nerve の豊穣関手へのアクセス。 -/
def cosliceFiberSimplex {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X _⦋n + 1⦌ :=
  SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫ s.val.val)

/-- 概要：最初の頂点を join に戻すと左包含になる。
方針：標準同型の順方向を右から消去して左包含の公式を使う。
規約：零単体からの射を比較する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の固定始点。 -/
lemma leftPointStdSimplexIso_first_inv (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      (leftPointStdSimplexIso.{u} n).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[n] := by
  apply (cancel_mono (leftPointStdSimplexIso n).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, joinStdSimplexIso_leftPoint_inl]

/-- 概要：最初の面を join に戻すと右包含になる。
方針：標準同型の順方向を右から消去して右包含の公式を使う。
規約：面の次数は n。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の底の条件。 -/
lemma leftPointStdSimplexIso_face_inv (n : ℕ) :
    stdSimplex.δ 0 ≫ (leftPointStdSimplexIso.{u} n).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n] := by
  apply (cancel_mono (leftPointStdSimplexIso n).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, joinStdSimplexIso_leftPoint_inr]

/-- 概要：coslice fiber の単体表示の最初の頂点は x。
方針：Yoneda の自然性で始点を join の左因子への制限として読む。
規約：全次数 n について成り立つ。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coherent な図式の始対象の固定。 -/
lemma cosliceFiberSimplex_source {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (cosliceFiberSimplex n s) = x := by
  change X.map _ (SSet.yonedaEquiv _) = x
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, leftPointStdSimplexIso_first_inv,
    s.val.property, Equiv.apply_symm_apply]

/-- 概要：coslice fiber の単体表示の最初の面は y に定値。
方針：最初の面の逆像は join の右因子なので fiber の固定条件を適用する。
規約：固定される面の次数は n。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coherent な図式の右側の定値性。 -/
lemma cosliceFiberSimplex_target {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X.δ 0 (cosliceFiberSimplex n s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n := by
  change X.map _ (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc]
  erw [leftPointStdSimplexIso_face_inv]
  exact s.property

/-- 概要：固定始点と定値な最初の面を持つ単体を coslice fiber に戻す。
方針：標準単体を join に移し、二つの条件を左右の制限に直す。
規約：最初の頂点は x、最初の面は y に定値。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、豊穣 Hom のデータから fiber の単体を作る。 -/
def cosliceFiberSimplexInverse {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌ := by
  refine ⟨⟨(leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm t.val, ?_⟩, ?_⟩
  · rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
      SSet.yonedaEquiv_symm_naturality_left, t.property.1]
  · change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n] ≫
      ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm t.val)) = _
    rw [← Category.assoc, joinStdSimplexIso_leftPoint_inr,
      stdSimplex.δ_comp_yonedaEquiv_symm, t.property.2, Equiv.apply_symm_apply]

/-- 概要：coslice fiber の n 単体と二つの固定条件を持つ (n+1) 単体は同値。
方針：join の標準同型と Yoneda の同値の逆写像則を使う。
規約：これは全次数の座標表示。写像空間との同値は高次の比較で別に証明する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、Construction 5.5.2.1（Tag 01ZW）、fiber の高次単体の比較。 -/
def cosliceFiberSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n} where
  toFun s := ⟨cosliceFiberSimplex n s,
    cosliceFiberSimplex_source n s, cosliceFiberSimplex_target n s⟩
  invFun := cosliceFiberSimplexInverse n
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫ s.val.val)) = s.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  right_inv s := by
    apply Subtype.ext
    change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm s.val)) = s.val
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：点との join の同型の逆は右因子の単体圏の射に自然。
方針：Core の順方向の自然性から同型を両側で消去する。
規約：元の添字写像には最初の頂点を固定する prependOrderHom を適用する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の座標の自然性。 -/
lemma leftPointStdSimplexIso_inv_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)) ≫
      (leftPointStdSimplexIso.{u} n).inv = (leftPointStdSimplexIso m).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α) := by
  dsimp only [leftPointStdSimplexIso]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Iso.inv_hom_id_assoc]

/-- 概要：coslice fiber の単体表示は面と退化の全ての引き戻しに自然。
方針：fiber の作用を join に沿う前合成と読み、標準同型の逆の自然性を使う。
規約：元の添字写像には最初の頂点を固定する延長を施す。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、fiber と coherent Hom の単体的比較。 -/
lemma cosliceFiberSimplex_naturality {X : SSet.{u}} {x y : X _⦋0⦌}
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    cosliceFiberSimplex m
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y).map α.op s) =
        X.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)).op
          (cosliceFiberSimplex n s) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso m).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫ s.val.val)) =
      X.map _ (SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫ s.val.val))
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc,
    ← leftPointStdSimplexIso_inv_naturality, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
