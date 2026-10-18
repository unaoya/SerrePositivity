module

public import SerrePositivity.InfinityCategories.F1.JoinStandardVertexRanges
public import SerrePositivity.InfinityCategories.F1.EdgewiseWeightCoordinates
public import SerrePositivity.InfinityCategories.F1.EdgewiseFaceImages
public import SerrePositivity.InfinityCategories.F1.EdgewiseKanExtension

/-!
概要：edgewise の境界面の像と標準単体内の二頂点を欠く面の同定。
方針：標準 join の頂点像を左右に分け、左の頂点の反転を追跡する。
規約：右延長領域の定義と同じ頂点番号を使う。
使われ方：Kerodon Corollary 8.1.1.13、境界接合領域と Kan 延長領域の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：重みの標準表示での左の欠落頂点は反転した左因子の面への所属と同値。
方針：標準 join の左頂点像の計算と反転した面の欠落条件を合成する。
規約：任意の単体次数 d を扱う。
使われ方：Kerodon Corollary 8.1.1.13、二頂点を欠く面の左条件。 -/
lemma edgewiseWeightIso_missing_left {n d : ℕ}
    (s : (edgewiseWeight.{u}.obj ⦋n⦌).obj (Opposite.op ⦋d⦌)) (i : Fin (n + 1)) :
    edgewiseLeftVertex n i ∉ Set.range ((edgewiseWeightIso n).hom.app (Opposite.op ⦋d⦌) s) ↔
      Join.augMem (stdSimplex.face ({i}ᶜ)).op s.1.val s.2.1 := by
  let t := (joinMap (stdSimplex.opIso ⦋n⦌).hom (𝟙 (Δ[n] : SSet.{u}))).app (Opposite.op ⦋d⦌) s
  have h := (joinStdSimplexIso_mem_range_left t i.rev).not
  have hv : Fin.cast (by omega : (n + 1) + (n + 1) = n + n + 1 + 1)
      (i.rev.castAdd (n + 1)) = edgewiseLeftVertex n i := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_rev, edgewiseLeftVertex]
    omega
  rw [hv] at h
  exact h.trans (Join.augMem_op_face_compl_iff i s.1.val s.2.1).symm

/-- 概要：重みの標準表示での右の欠落頂点は右因子の面への所属と同値。
方針：標準 join の右頂点像の計算と面の欠落条件を合成する。
規約：右因子の頂点番号は反転しない。
使われ方：Kerodon Corollary 8.1.1.13、二頂点を欠く面の右条件。 -/
lemma edgewiseWeightIso_missing_right {n d : ℕ}
    (s : (edgewiseWeight.{u}.obj ⦋n⦌).obj (Opposite.op ⦋d⦌)) (i : Fin (n + 1)) :
    edgewiseRightVertex n i ∉ Set.range ((edgewiseWeightIso n).hom.app (Opposite.op ⦋d⦌) s) ↔
      Join.augMem (stdSimplex.face ({i}ᶜ)) (d + 1 - s.1.val) s.2.2 := by
  let t := (joinMap (stdSimplex.opIso ⦋n⦌).hom (𝟙 (Δ[n] : SSet.{u}))).app (Opposite.op ⦋d⦌) s
  have h := (joinStdSimplexIso_mem_range_right t i).not
  have hv : Fin.cast (by omega : (n + 1) + (n + 1) = n + n + 1 + 1)
      (i.natAdd (n + 1)) = edgewiseRightVertex n i := by
    apply Fin.ext
    rfl
  rw [hv] at h
  change edgewiseRightVertex n i ∉ Set.range ((edgewiseWeightIso n).hom.app (Opposite.op ⦋d⦌) s) ↔
    i ∉ Set.range (Join.stdAugEquiv n (d + 1 - s.1.val)
      (Join.augHom (𝟙 (Δ[n] : SSet.{u})) (d + 1 - s.1.val) s.2.2)) at h
  rw [Join.augHom_id] at h
  exact h.trans (Join.augMem_face_compl_iff i (d + 1 - s.1.val) s.2.2).symm

/-- 概要：標準単体内の対応する二頂点を欠く面の逆像は edgewise の境界面の像。
方針：二つの頂点の不在を左右の面への所属に変え、既存の面の像の式を使う。
規約：全体の次数は n+1。
使われ方：Kerodon Corollary 8.1.1.13、延長領域の各面を接合の被覆へ同定する。 -/
lemma edgewiseWeightIso_pair_face_preimage (n : ℕ) (i : Fin (n + 2)) :
    (stdSimplex.face ({edgewiseLeftVertex (n + 1) i, edgewiseRightVertex (n + 1) i}ᶜ)).preimage
      (edgewiseWeightIso.{u} (n + 1)).hom =
    Subcomplex.range (edgewiseWeight.map (SimplexCategory.δ i)) := by
  rw [edgewiseWeight_face_range]
  ext ⟨⟨d⟩⟩ s
  change (edgewiseWeightIso (n + 1)).hom.app (Opposite.op ⦋d⦌) s ∈
      (stdSimplex.face ({edgewiseLeftVertex (n + 1) i, edgewiseRightVertex (n + 1) i}ᶜ)).obj _ ↔
    s ∈ (joinSubcomplexLeft (stdSimplex.face ({i}ᶜ)).op Δ[n + 1]).obj _ ∧
      s ∈ (joinSubcomplexRight (Δ[n + 1] : SSet.{u}).op (stdSimplex.face ({i}ᶜ))).obj _
  rw [stdSimplex.mem_face_iff, Join.mem_joinSubcomplexLeft, Join.mem_joinSubcomplexRight]
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, forall_and]
  have hl := edgewiseWeightIso_missing_left s i
  have hr := edgewiseWeightIso_missing_right s i
  simp only [Set.mem_range, not_exists] at hl hr
  exact and_congr hl hr

/-- 概要：標準単体内の右全面の逆像は重みの右包含の像。
方針：右包含の標準表示の像の式と同型による像・逆像の往復を使う。
規約：全ての次数 n で成立する。
使われ方：Kerodon Corollary 8.1.1.13、固定した右半分の接合領域の同定。 -/
lemma edgewiseWeightIso_right_face_preimage (n : ℕ) :
    (stdSimplex.face (edgewiseRightVertices n)).preimage (edgewiseWeightIso.{u} n).hom =
      Subcomplex.range (joinInr (Δ[n] : SSet.{u}).op Δ[n]) := by
  rw [← edgewiseWeightIso_inr_range, Subcomplex.range_comp, Subcomplex.preimage_image]

end SerrePositivity.InfinityCategories
