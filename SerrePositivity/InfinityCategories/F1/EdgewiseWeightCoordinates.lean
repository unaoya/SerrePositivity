module

public import SerrePositivity.InfinityCategories.F1.EdgewiseExtensionDomain
public import SerrePositivity.InfinityCategories.DGNerve.JoinSimplexInclusions

/-!
概要：edgewise の重みの両因子の標準単体表示と、右因子の像の面の同定。
方針：既存の join の左右の包含の計算を再利用し、右頂点集合を有限順序と同定する。
規約：DGNerve のファイルは参照のみ。
使われ方：Kerodon Notation 8.1.1.6、Corollary 8.1.1.13、境界充填の固定する右半分の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：重みの左包含は反転同型と標準単体の左区間の包含の合成になる。
方針：join の左包含の自然性と既存の標準単体の join の座標式を使う。
規約：左因子の標準単体の反転同型を明示する。
使われ方：Kerodon Remark 8.1.1.2、境界面の左側の番号の照合。 -/
lemma edgewiseWeightIso_inl (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom =
      (stdSimplex.opIso ⦋n⦌).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (DGNerve.joinLeftOrderHom n n)) := by
  change joinInl _ _ ≫ joinMap (stdSimplex.opIso ⦋n⦌).hom (𝟙 Δ[n]) ≫
    (joinStdSimplexIso n n).hom = _
  rw [joinInl_joinMap_assoc, DGNerve.joinStdSimplexIso_inl]

/-- 概要：重みの右包含は標準単体の後半の区間の包含になる。
方針：join の右包含の自然性と既存の標準単体の join の座標式を使う。
規約：頂点番号は n+1 だけずらす。
使われ方：Kerodon Notation 8.1.1.6、右射影で固定する部分の座標。 -/
lemma edgewiseWeightIso_inr (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom =
      stdSimplex.map (SimplexCategory.mkHom (DGNerve.joinRightOrderHom n n)) := by
  change joinInr _ _ ≫ joinMap (stdSimplex.opIso ⦋n⦌).hom (𝟙 Δ[n]) ≫
    (joinStdSimplexIso n n).hom = _
  rw [joinInr_joinMap_assoc, Category.id_comp, DGNerve.joinStdSimplexIso_inr]

/-- 概要：右半分の頂点集合は Fin(n+1) と順序同型。
方針：n+1 を加える写像と、それを引く写像を互いに逆とする。
規約：頂点集合には標準の誘導順序を使う。
使われ方：Kerodon Notation 8.1.1.6、右半分の面の標準単体表示。 -/
def edgewiseRightVerticesOrderIso (n : ℕ) : Fin (n + 1) ≃o edgewiseRightVertices n where
  toFun i := ⟨edgewiseRightVertex n i, by
    simp only [edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ,
      true_and, edgewiseRightVertex]
    omega⟩
  invFun v := ⟨v.val.val - (n + 1), by
    have hv := v.val.isLt
    have hn := v.property
    simp only [edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp [edgewiseRightVertex]
    omega
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hn := v.property
    simp only [edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    dsimp [edgewiseRightVertex]
    omega
  map_rel_iff' := by
    intro i j
    change n + 1 + i.val ≤ n + 1 + j.val ↔ i.val ≤ j.val
    omega

/-- 概要：右因子の重みの標準単体内での像は右頂点集合の全面。
方針：右包含の座標式と、右頂点集合の順序同型による面の表示を使う。
規約：部分複体としての厳密な等式。
使われ方：Kerodon Corollary 8.1.1.13、有限な延長領域と右射影の固定条件の接続。 -/
lemma edgewiseWeightIso_inr_range (n : ℕ) :
    Subcomplex.range (joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom) =
      stdSimplex.face (edgewiseRightVertices n) := by
  rw [edgewiseWeightIso_inr, Subcomplex.range_eq_ofSimplex]
  exact (stdSimplex.face_eq_ofSimplex (edgewiseRightVertices n) n
    (edgewiseRightVerticesOrderIso n)).symm

end SerrePositivity.InfinityCategories
