module
public import SerrePositivity.KST.SConstruction.ArTwoMiddleSquare

/-! # 中央正方形の外の単体の端点
概要：Ar[2] の中央正方形に入らない鎖は、最初か最後に外側の零対角を持つ。
方針：中央四頂点への切り詰めの逆律と、順序の最小・最大対象を使う。
規約：退化鎖も含む。使われ方：BGT Lemma 7.3 の始点・終点による補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Ar[2] の対象は外側の両対角か中央の四頂点に属する。
方針：二つの Fin 3 の全ての場合を検査する。
規約：中央条件は左端≤1かつ1≤右端。使われ方：新しい単体の端点の判定。 -/
lemma arTwo_obj_middle_or_endpoint (a : Ar.{u} 2) :
    a = arObj 0 0 le_rfl ∨ a = arObj 2 2 le_rfl ∨
      (a.down.val.1 ≤ 1 ∧ 1 ≤ a.down.val.2) := by
  rcases a with ⟨⟨⟨i, j⟩, h⟩⟩
  change i.val ≤ j.val at h
  fin_cases i <;> fin_cases j <;> simp_all [arObj, Fin.le_def]
  all_goals exact Nat.not_succ_le_zero _ h

/-- 概要：中央の対象は切り詰めてから正方形に戻すと元に戻る。
方針：中央の四つの対象を計算する。
規約：順序関手の対象での厳密等号。使われ方：中央を頂点とする鎖の像への所属。 -/
lemma arTwoMiddleRetraction_obj_back (a : Ar.{u} 2)
    (ha : a.down.val.1 ≤ 1) (hb : 1 ≤ a.down.val.2) :
    (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor.obj
      (arTwoMiddleRetractionOrder.toFunctor.obj a) = a := by
  rcases a with ⟨⟨⟨i, j⟩, h⟩⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [arSquareOrder, arTwoMiddleRetractionOrder, intervalStep, arObj]

/-- 概要：切り詰めて包含する射は二つの順序関手の合成の nerve。
方針：標準単体の積の同型の逆律を消去する。
規約：全次数での射の等号。使われ方：鎖ごとの像の所属の証明。 -/
lemma arTwoMiddleRetraction_square :
    arTwoMiddleRetraction.{u} ≫ arTwoMiddleSquare =
      nerveMap (arTwoMiddleRetractionOrder.toFunctor ⋙
        (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor) := by
  change (nerveMap arTwoMiddleRetractionOrder.toFunctor ≫ (prodStdSimplex.isoNerve 1 1).inv) ≫
    ((prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap
      (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- 概要：全頂点が中央に属する鎖は中央正方形の像に入る。
方針：切り詰めた正方形単体を取り、その像が元の鎖に一致することを示す。
規約：次数は任意。使われ方：中央部分から外れる単体の判定。 -/
lemma arTwoMiddle_mem_of_vertices {d : ℕ} (s : (arNerve.{u} 2) _⦋d⦌)
    (hs : ∀ r, (s.obj r).down.val.1 ≤ 1 ∧ 1 ≤ (s.obj r).down.val.2) :
    s ∈ arTwoMiddle.obj (Opposite.op ⦋d⦌) := by
  refine ⟨arTwoMiddleRetraction.app (Opposite.op ⦋d⦌) s, ?_⟩
  change (arTwoMiddleRetraction ≫ arTwoMiddleSquare).app (Opposite.op ⦋d⦌) s = s
  rw [arTwoMiddleRetraction_square]
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact arTwoMiddleRetraction_obj_back (s.obj r) (hs r).1 (hs r).2

/-- 概要：中央正方形の像の鎖の各頂点は中央の端点条件を満たす。
方針：正方形単体の像として表示して二つの区間の上下界を使う。
規約：次数は任意。使われ方：両端の外側対角が像に属さないこと。 -/
lemma arTwoMiddle_vertices_of_mem {d : ℕ} (s : (arNerve.{u} 2) _⦋d⦌)
    (hs : s ∈ arTwoMiddle.obj (Opposite.op ⦋d⦌)) (r : Fin (d + 1)) :
    (s.obj r).down.val.1 ≤ 1 ∧ 1 ≤ (s.obj r).down.val.2 := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨intervalStep_le (0 : Fin 3) 1 (by decide) _,
    le_intervalStep (1 : Fin 3) 2 (by decide) _⟩

/-- 概要：最初の零対角は中央正方形の像に含まれない。
方針：中央の右端は1以上という条件に反する。
規約：零単体での主張。使われ方：新しい零頂点の指定。 -/
lemma arTwoMiddle_notMem_first :
    ComposableArrows.mk₀ (arObj (0 : Fin 3) 0 le_rfl) ∉
      arTwoMiddle.{u}.obj (Opposite.op ⦋0⦌) := by
  intro h
  have hh := (arTwoMiddle_vertices_of_mem _ h 0).2
  exact (by decide : ¬ (1 : Fin 3) ≤ 0) hh

/-- 概要：最後の零対角は中央正方形の像に含まれない。
方針：中央の左端は1以下という条件に反する。
規約：零単体での主張。使われ方：新しい零頂点の指定。 -/
lemma arTwoMiddle_notMem_last :
    ComposableArrows.mk₀ (arObj (2 : Fin 3) 2 le_rfl) ∉
      arTwoMiddle.{u}.obj (Opposite.op ⦋0⦌) := by
  intro h
  have hh := (arTwoMiddle_vertices_of_mem _ h 0).1
  exact (by decide : ¬ (2 : Fin 3) ≤ 1) hh

/-- 概要：中央正方形の外にある鎖は最小または最大の対角を端点に持つ。
方針：両端が外側の対角でなければ、単調性から全頂点が中央に属する。
規約：零次元も含む。使われ方：新しい単体に対する始対象・終対象の充填。 -/
lemma arTwoMiddle_missing_endpoint {d : ℕ} (s : (arNerve.{u} 2) _⦋d⦌)
    (hs : s ∉ arTwoMiddle.obj (Opposite.op ⦋d⦌)) :
    s.obj 0 = arObj 0 0 le_rfl ∨ s.obj (Fin.last d) = arObj 2 2 le_rfl := by
  by_contra h
  push Not at h
  apply hs
  apply arTwoMiddle_mem_of_vertices
  intro r
  rcases arTwo_obj_middle_or_endpoint (s.obj r) with hr | hr | hr
  · have he : s.obj 0 = arObj 0 0 le_rfl := by
      apply le_antisymm
      · exact hr ▸ s.monotone (Fin.zero_le r)
      · exact ⟨Fin.zero_le _, Fin.zero_le _⟩
    exact False.elim (h.1 he)
  · have he : s.obj (Fin.last d) = arObj 2 2 le_rfl := by
      apply le_antisymm
      · exact ⟨Fin.le_last _, Fin.le_last _⟩
      · exact hr ▸ s.monotone (Fin.le_last r)
    exact False.elim (h.2 he)
  · exact hr

end SerrePositivity.KST.SConstruction
