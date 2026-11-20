module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryRelation

/-!
概要：球面的境界の最後の面の代表を同じホモトピー類の代表へ変える。
方針：元の単体、RelStruct と他の面の退化を一つ高いホーンへ置く。
規約：最後以外の面は厳密に保持する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。交代和の零性から境界充填へ戻す。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.SphericalBoundaryLastFace
end SerrePositivity.KST.Spectra.SphericalBoundaryLastFace
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：RelStruct の全ての面を計算する。
方針：二つの指定面と外側の定数面に分ける。
規約：指定面の順序は第一代表、第二代表。
使われ方：Kerodon §3.2.3（Tag 00W3）。代表変更の高次ホーン。 -/
theorem SimplexFaces.rel_face {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : PtSimplex.RelStruct f g i)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ r.map = if j = i.castSucc then f.map else
      if j = i.succ then g.map else SSet.const x := by
  by_cases h0 : j = i.castSucc
  · subst j; simp
  by_cases h1 : j = i.succ
  · subst j; simp [h0]
  rw [ite_eq_right h0, ite_eq_right h1]
  by_cases hj : j < i.castSucc
  · exact r.δ_map_of_lt j hj
  · exact r.δ_map_of_gt j (by grind)

namespace SphericalBoundaryLastFace
open _root_.SerrePositivity.KST.Spectra.SphericalBoundaryLastFace

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {a : Fin (n + 4) → X.PtSimplex (n + 2) x} {b : X.PtSimplex (n + 2) x}

/-- 概要：最後の面を変更するホーンの面の族。
方針：元の単体と RelStruct の間に欠ける面を置き、前の各面は退化させる。
規約：欠ける面は n + 3。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。代表変更の充填。 -/
def face (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (r : PtSimplex.RelStruct (a (Fin.last (n + 3))) b (Fin.last (n + 2)))
    (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n + 2 then T.map else
  if j.val = n + 4 then r.map else
  if hj : j.val < n + 2 then
    stdSimplex.σ (Fin.last (n + 1)).castSucc ≫ (a ⟨j.val, by omega⟩).map
  else SSet.const x

/-- 概要：最後の面を変更するホーンは互換である。
方針：元の境界と RelStruct と退化の面を直接計算する。
規約：n + 3 の面を除いた互換性。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。Kan 性の適用条件。 -/
theorem compatible (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (r : PtSimplex.RelStruct (a (Fin.last (n + 3))) b (Fin.last (n + 2))) :
    horn.IsCompatible (i := (Fin.last (n + 3)).castSucc) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.face T r j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 3 := fun he ↦ hk (Fin.ext he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.rel_face,
    T.face_eq, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (apply congrArg (fun t ↦ (a t).map)
       apply Fin.ext
       simp only [Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ,
         Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 概要：代表変更のホーンの欠ける面の境界を計算する。
方針：二面交換で既知の面へ移し、最後以外の面と最後の新しい面を読む。
規約：φ はホーンの実際の充填。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。最後の面だけの変更。 -/
theorem output_face (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (r : PtSimplex.RelStruct (a (Fin.last (n + 3))) b (Fin.last (n + 2)))
    (φ : (Δ[n + 4] : SSet.{u}) ⟶ X)
    (hφ : ∀ (j : Fin (n + 5)) (_ : j ≠ (Fin.last (n + 3)).castSucc),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.face T r j) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 3)).castSucc ≫ φ =
      if j = Fin.last (n + 3) then b.map else (a j).map := by
  by_cases hj : j ≤ (Fin.last (n + 2)).castSucc
  · rw [show (Fin.last (n + 3)).castSucc = (Fin.last (n + 2)).castSucc.succ from rfl,
      stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.rel_face,
      T.face_eq, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (apply congrArg (fun t ↦ (a t).map)
         apply Fin.ext
         try simp only [Fin.val_castSucc, Fin.val_last] at *
         omega)
      | (exfalso
         simp_all only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_succ, Fin.val_last, or_true, not_true_eq_false] <;> omega)
  · have he : j = Fin.last (n + 3) := by
      apply Fin.ext
      change j.val = n + 3
      have hj' : ¬j.val ≤ n + 2 := hj
      omega
    subst j
    rw [ite_eq_left rfl]
    have hm : (Fin.last (n + 2)).succ ≤ (Fin.last (n + 3)) := by grind
    rw [show (Fin.last (n + 3)).castSucc = (Fin.last (n + 2)).succ.castSucc from rfl,
      ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.face, Fin.val_succ, Fin.val_last]
    rw [ite_eq_right (by omega)]
    simp only [ite_true]
    exact r.δ_succ_map

/-- 概要：最後の面を関係する代表へ変えた球面的境界を構成する。
方針：互換な比較ホーンを Kan 充填し、その欠ける面を取る。
規約：Function.update により最後以外の面は厳密に同じ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。境界充填の代表独立性。 -/
noncomputable def replace [KanComplex X] (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (r : PtSimplex.RelStruct (a (Fin.last (n + 3))) b (Fin.last (n + 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary (Function.update a (Fin.last (n + 3)) b) where
  map := stdSimplex.δ (Fin.last (n + 3)).castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.compatible T r).liftOfKanComplex
  face_eq j := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.output_face T r _ (fun k hk ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.compatible T r).δ_liftOfKanComplex k hk)]
    by_cases hj : j = Fin.last (n + 3) <;> simp [hj]

/-- 概要：最後の面を同じホモトピー類の任意の代表へ変更できる。
方針：商の等式から最後の添字の RelStruct を選んで比較ホーンを埋める。
規約：存在は追加仮定ではなく Kan 性から従う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。交代和による充填条件。 -/
theorem exists_replace [KanComplex X] (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a (Fin.last (n + 3))) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary (Function.update a (Fin.last (n + 3)) b)) := by
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 2))).1
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).1 h)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.replace T r⟩

end SphericalBoundaryLastFace

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
