module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan fibration のホモトピー長完全列の完全性。
方針：核の元の零ホモトピーを相対充填し、直前の射の具体的な原像を構成する。
規約：追加の完全性仮定を導入せず、代表単体と RelStruct の計算を行う。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）、Goerss–Jardine I §§7–8。L9b の完全性。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.FiberExactness
end SerrePositivity.KST.Spectra.FiberExactness
namespace SerrePositivity.KST.Spectra.TotalExactness
end SerrePositivity.KST.Spectra.TotalExactness
namespace SerrePositivity.KST.Spectra.BaseExactness
end SerrePositivity.KST.Spectra.BaseExactness
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

namespace FiberExactness
open _root_.SerrePositivity.KST.Spectra.FiberExactness

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex B]
  (e : E _⦋0⦌) {n : ℕ}

/-- 概要：fiber の代表の全空間での零ホモトピーから、連結写像の原像を構成する。
方針：零ホモトピーを底へ射影して境界定数単体を作り、同じ単体を相対持ち上げとする。
規約：fiber の代表の次数は n、底の原像の次数は n + 1。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。零次数も含む fiber の核が連結射の像に含まれること。 -/
theorem exists_connecting_of_nullRel_all
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e))
    (r : PtSimplex.RelStruct RelativeMorphism.const
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b) (Fin.last n)) :
    ∃ s : B.PtSimplex (n + 1) (p.app _ e),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n b := by
  have hlast : stdSimplex.δ (Fin.last (n + 1)) ≫ r.map = b.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) := by
    simpa only [Fin.succ_last, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_map] using r.δ_succ_map
  have hr (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
      stdSimplex.δ j ≫ r.map = SSet.const e := by
    by_cases he : j = (Fin.last n).castSucc
    · subst j; exact r.δ_castSucc_map
    · have hj' : j.val ≠ n + 1 := fun h ↦ hj (Fin.ext h)
      apply r.δ_map_of_lt
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
      have he' : j.val ≠ n := fun h ↦ he (Fin.ext h)
      omega
  let s : B.PtSimplex (n + 1) (p.app _ e) :=
    { map := r.map ≫ p
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        by_cases hj : j = Fin.last (n + 1)
        · subst j
          rw [← Category.assoc, hlast, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, comp_const]
        · rw [← Category.assoc, hr j hj, const_comp] }
  let L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s := { map := r.map, map_comp := rfl, face_eq := hr }
  have hb : L.boundary = b := by
    ext : 1
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    rw [L.boundary_ι]
    exact hlast
  refine ⟨s, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L, hb]

/-- 概要：fiber の正次数の零ホモトピーから底の原像を得る。
方針：零次数を含む一般の構成を正次数に適用する。
規約：fiber の次数は n + 1、底の原像の次数は n + 2。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。正次数の完全性の界面。 -/
theorem exists_connecting_of_nullRel
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e))
    (r : PtSimplex.RelStruct RelativeMorphism.const
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b) (Fin.last (n + 1))) :
    ∃ s : B.PtSimplex (n + 2) (p.app _ e),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberExactness.exists_connecting_of_nullRel_all p e b r

end FiberExactness

namespace TotalExactness
open _root_.SerrePositivity.KST.Spectra.TotalExactness

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) {n : ℕ}

/-- 概要：全空間の代表の底での零ホモトピーから fiber の代表と RelStruct を作る。
方針：底の零ホモトピーを相対ホーンに沿って持ち上げ、最後の面を fiber へ送る。
規約：代表単体の次数は n + 1。Kan 性は fibration の RLP にのみ使う。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。全空間の位置の核が fiber の像に含まれること。 -/
theorem exists_fiber_of_baseNullRel (a : E.PtSimplex (n + 1) e)
    (r : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl a) RelativeMorphism.const (Fin.last (n + 1))) :
    ∃ b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e),
      Nonempty (PtSimplex.RelStruct a
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b) (Fin.last (n + 1))) := by
  let α (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
    if j.val = n + 1 then a.map else SSet.const e
  have hαface (j) (hj) (k : Fin (n + 2)) : stdSimplex.δ k ≫ α j hj = SSet.const e := by
    dsimp [α]; split_ifs <;> simp
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [hαface]
  have hcomm (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      α j hj ≫ p = stdSimplex.δ j ≫ r.map := by
    by_cases hj₀ : j.val = n + 1
    · have he : j = (Fin.last (n + 1)).castSucc := Fin.ext hj₀
      dsimp [α]
      rw [ite_eq_left hj₀, he]
      exact r.δ_castSucc_map.symm
    · have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
      have hlt : j < (Fin.last (n + 1)).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        omega
      dsimp [α]
      rw [ite_eq_right hj₀, const_comp, r.δ_map_of_lt j hlt]
  obtain ⟨φ, hφ, hp⟩ := hα.exists_lift p r.map hcomm
  have ht : (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = SSet.const (p.app _ e) := by
    rw [Category.assoc, hp]
    simpa only [Fin.succ_last, RelativeMorphism.const_map] using r.δ_succ_map
  let b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
    { map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ht
      comm := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, Subcomplex.ofSimplex_ι, comp_const,
          const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
        ext j : 1
        simp only [boundary.ι_ι_assoc, comp_const]
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hφ _ (Fin.castSucc_ne_last j)]
        exact hαface _ (Fin.castSucc_ne_last j) _ }
  refine ⟨b, ⟨{
    map := φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · simpa [α] using hφ (Fin.last (n + 1)).castSucc (Fin.castSucc_ne_last _)
  · rw [Fin.succ_last]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ht).symm
  · intro j hj
    rw [hφ j (Fin.ne_last_of_lt (hj.trans (Fin.castSucc_lt_last _)))]
    dsimp [α]
    apply ite_eq_right
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
    omega
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：底で基点と同じ成分へ写る零単体は、fiber の零単体と辺で結ばれる。
方針：底の辺を、全空間の指定した終点を固定して持ち上げる。
規約：零次数の関係の向きに合わせ、終点を与えた外ホーンを使う。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。π₀(全空間) の位置の完全性。 -/
theorem exists_fiber_of_baseNullRel_zero (a : E.PtSimplex 0 e)
    (r : PtSimplex.RelStruct₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl a) RelativeMorphism.const) :
    ∃ b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e),
      Nonempty (PtSimplex.RelStruct₀ a
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b)) := by
  let α (j : Fin 2) (_ : j ≠ (1 : Fin 2)) : (Δ[0] : SSet.{u}) ⟶ E := a.map
  have hα : horn.IsCompatible α := by simp
  have hcomm (j : Fin 2) (hj : j ≠ 1) : α j hj ≫ p = stdSimplex.δ j ≫ r.map := by
    have he : j = 0 := by
      apply Fin.ext
      have hn : j.val ≠ 1 := fun h ↦ hj (Fin.ext h)
      omega
    subst j
    exact r.δ_castSucc_map.symm
  obtain ⟨φ, hφ, hp⟩ := hα.exists_lift p r.map hcomm
  have ht : (stdSimplex.δ (1 : Fin 2) ≫ φ) ≫ p = SSet.const (p.app _ e) := by
    rw [Category.assoc, hp]
    exact r.δ_succ_map
  let b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
    { map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (stdSimplex.δ (1 : Fin 2) ≫ φ) ht
      comm := by ext }
  refine ⟨b, ⟨{
    map := φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · exact hφ 0 (by decide)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p (p.app _ e) (stdSimplex.δ (1 : Fin 2) ≫ φ) ht).symm
  · intro j hj; exact (Fin.not_lt_zero j hj).elim
  · intro j hj; exact (not_lt_of_ge (Fin.le_last j) hj).elim

end TotalExactness

namespace BaseExactness
open _root_.SerrePositivity.KST.Spectra.BaseExactness

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}

/-- 概要：fiber の零ホモトピーの全空間側の面を計算する。
方針：最後から二番目の面だけが元の代表で、それ以外は基点に定数となる。
規約：r は境界代表から定数代表への RelStruct。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。底の位置の完全性の貼り合わせ。 -/
theorem rel_face (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ r.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) =
      if j.val = n then L.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e := by
  by_cases hj : j.val = n
  · have he : j = (Fin.last n).castSucc := Fin.ext hj
    rw [ite_eq_left hj, he, r.δ_castSucc_map_assoc]
  · rw [ite_eq_right hj]
    by_cases hj' : j = Fin.last (n + 1)
    · subst j
      have he := r.δ_succ_map
      simp only [Fin.succ_last] at he
      rw [← Category.assoc, he]
      simp
    · have hlt : j < (Fin.last n).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        have hk : j.val ≠ n + 1 := fun h ↦ hj' (Fin.ext h)
        omega
      rw [r.δ_map_of_lt_assoc j hlt, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]

/-- 概要：底の代表の持ち上げと fiber 内の零ホモトピーを貼るホーンの面。
方針：n 番目に持ち上げ、n + 2 番目に零ホモトピーを置く。
規約：欠ける面は n + 1。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。底の核の元の全空間への持ち上げ。 -/
noncomputable def face (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
  if j.val = n then L.map else
  if j.val = n + 2 then r.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e

/-- 概要：底の完全性のホーンの面は互換である。
方針：持ち上げの最後の面と fiber の零ホモトピーの最初の面が一致することを使う。
規約：n + 1 番目の面を除く。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。全空間での Kan 充填。 -/
theorem compatible (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n)) :
    horn.IsCompatible (i := (Fin.last n).castSucc.succ) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face L r j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face]
  split_ifs <;> try simp only [L.face_formula, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.rel_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：貼り合わせホーンの欠ける面は全ての境界で基点に定数となる。
方針：二面を交換して、持ち上げの定数面か零ホモトピーの定数面へ移す。
規約：φ は貼り合わせホーンの実際の充填。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。全空間のホモトピー群の代表の構成。 -/
theorem output_face (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n))
    (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ (Fin.last n).castSucc.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face L r j) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last n).castSucc.succ ≫ φ = SSet.const e := by
  by_cases hj : j ≤ (Fin.last n).castSucc
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face]
    split_ifs <;> try simp only [L.face_formula, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_last] at *
         first | tauto | omega)
  · have hm : (Fin.last n).succ ≤ j := by grind
    have he : (Fin.last n).castSucc.succ = (Fin.last n).succ.castSucc := by
      apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.rel_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_last, Fin.val_succ] at *
         first | tauto | omega)

/-- 概要：連結射の境界代表が fiber 内で零なら、底の類は全空間の類の像となる。
方針：持ち上げと零ホモトピーを Kan ホーンで貼り、底で単位積の充填を得る。
規約：底の代表の次数は n + 1。fiber の零次数も幾何的には許す。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。底の位置の完全性。 -/
theorem exists_total_of_boundaryNullRel [Fibration p] [KanComplex E] [KanComplex B]
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (r : PtSimplex.RelStruct L.boundary RelativeMorphism.const (Fin.last n)) :
    ∃ a : E.PtSimplex (n + 1) e,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s := by
  let φ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.compatible L r).liftOfKanComplex
  have hφ : ∀ (j : Fin (n + 3)) (_ : j ≠ (Fin.last n).castSucc.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face L r j := fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.compatible L r).δ_liftOfKanComplex j hj
  let a : E.PtSimplex (n + 1) e :=
    { map := stdSimplex.δ (Fin.last n).castSucc.succ ≫ φ
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.output_face L r φ hφ j }
  have hmul : PtSimplex.MulStruct RelativeMorphism.const s (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl a) (Fin.last n) :=
    { map := φ ≫ p
      δ_castSucc_castSucc_map := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face, L.map_comp]
      δ_succ_castSucc_map := rfl
      δ_succ_succ_map := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face, Fin.val_succ, Fin.val_last]
        rw [ite_eq_right (by omega)]
        simp
      δ_map_of_lt j hj := by
        rw [← Category.assoc, hφ _ (by grind)]
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face]
        split_ifs <;> first
          | exact const_comp _ _
          | (exfalso
             simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
             omega)
      δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim }
  refine ⟨a, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hmul
  change (1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e)) * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl a) at hm
  simpa only [one_mul] using hm.symm

end BaseExactness

/-- 概要：fiber の正次数で包含の核は連結写像の像と一致する。
方針：全空間で零となる代表の RelStruct から底の原像を作り、逆向きは複体条件を使う。
規約：fiber の実際の次数は n + 1、底の原像の次数は n + 2。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の fiber の正次数での完全性。 -/
@[kerodon 00WM, kerodon 00WQ]
theorem exact_connecting_fiber {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) b = a := by
  induction a using Quotient.inductionOn with | h b => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b) = 1 ↔
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b
  constructor
  · intro h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk] at h
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (RelativeMorphism.const : E.PtSimplex (n + 1) e) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b) := h.symm
    have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).1 he
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberExactness.exists_connecting_of_nullRel p e b r
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s, hs⟩
  · rintro ⟨c, hc⟩
    have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_map_connecting p e (n + 1) c
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) c) = 1 at hz
    rw [hc] at hz
    exact hz

/-- 概要：全空間の正次数で射影の核は fiber の包含の像と一致する。
方針：底の零ホモトピーを相対充填して fiber の原像を作る。
規約：全空間と fiber の実際の次数は n + 1。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の全空間の位置の完全性。 -/
@[kerodon 00WN]
theorem exact_fiber_total {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E n e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b = a := by
  constructor
  · intro ha
    induction a using Quotient.inductionOn with | h s => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1 at ha
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk] at ha
    have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) .const).1 ha
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨b, ⟨hb⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.TotalExactness.exists_fiber_of_baseNullRel p e s r
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b, ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound hb).symm
  · rintro ⟨b, rfl⟩
    induction b using Quotient.inductionOn with | h s => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) s) =
        RelativeMorphism.const := by
      ext : 1
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
    rw [hc]
    rfl

/-- 概要：底の二以上の次数で連結射の核は全空間からの射影の像と一致する。
方針：fiber で零となる境界の RelStruct を貼り合わせ、全空間の代表を構成する。
規約：底の実際の次数は n + 2。零次数の標的に対する端の完全性は別に扱う。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の底の位置の完全性。 -/
@[kerodon 00WM, kerodon 00WS]
theorem exact_total_base {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E (n + 1) e, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl b = a := by
  constructor
  · intro ha
    induction a using Quotient.inductionOn with | h s => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1 at ha
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L] at ha
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk L.boundary = 1 at ha
    have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff L.boundary .const).1 ha
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 1))).1 hr
    obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.exists_total_of_boundaryNullRel L r
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b, hb⟩
  · rintro ⟨b, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_map p e (n + 1) b

/-- 概要：fiber の零次数を含む全次数で、包含の基点の逆像は連結写像の像。
方針：全空間での零ホモトピーから底の原像を構成し、逆向きは複体条件を使う。
規約：n = 0 は基点付き集合の完全性、n > 0 は群の核と像の一致。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。π₀(fiber) を含む長完全列の端。 -/
@[kerodon 00WQ]
theorem exact_connecting_fiber_all {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n b = a := by
  constructor
  · intro ha
    obtain ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk] at ha
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (RelativeMorphism.const : E.PtSimplex n e) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const n).trans ha.symm
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ (Fin.last n)).1 he
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberExactness.exists_connecting_of_nullRel_all p e b r
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s, hs⟩
  · rintro ⟨b, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_map_connecting p e n b

/-- 概要：底の π₁ を含む全正次数で、連結像が基点となる元は全空間から来る。
方針：零次数でも単一の RelStruct に戻せることを使い、境界の零ホモトピーを貼る。
規約：n = 0 の標的は π₀(fiber) であり、群構造を要求しない。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。π₁(B) → π₀(fiber) の位置の完全性。 -/
@[kerodon 00WS]
theorem exact_total_base_all {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E n e, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl b = a := by
  constructor
  · intro ha
    induction a using Quotient.inductionOn with | h s => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n at ha
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L] at ha
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n L.boundary = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n RelativeMorphism.const :=
      ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const n).symm
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ (Fin.last n)).1 he
    obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.exists_total_of_boundaryNullRel L r
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b, hb⟩
  · rintro ⟨b, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_map p e n b

/-- 概要：π₀(全空間) で、底の基点の成分の逆像は fiber からの像。
方針：底の成分の等式を一本の辺へ戻し、終点を指定して持ち上げる。
規約：群の核ではなく基点付き集合の完全性として述べる。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。長完全列の零次数の端。 -/
theorem exact_fiber_total_zero {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E 0 e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 p rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b = a := by
  constructor
  · intro ha
    obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective 0 a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk] at ha
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 RelativeMorphism.const :=
      ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const 0).symm
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct 0 _ _ 0).1 he
    obtain ⟨b, ⟨hb⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.TotalExactness.exists_fiber_of_baseNullRel_zero p e s r
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 b, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.sound hb).symm
  · rintro ⟨b, rfl⟩
    obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective 0 b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) s) =
        RelativeMorphism.const := by
      ext : 1
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
    rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const]

/-- 概要：全空間の全自然数次数で、射影の基点の逆像は fiber の包含の像。
方針：正次数の群の完全性と零次数の辺の持ち上げをまとめる。
規約：零次数には群構造を要求しない。
使われ方：Kerodon Theorem 3.2.6.1（Tag 00WM）。全次数のホモトピー長完全列。 -/
@[kerodon 00WN]
theorem exact_fiber_total_all {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E n e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n p rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b = a := by
  cases n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_zero p e a
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total p e n a

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_connecting_fiber := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_connecting_fiber_all := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber_all

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_fiber_total := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_fiber_total_all := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_all

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_fiber_total_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_total_base := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exact_total_base_all := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base_all

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.compatible := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.compatible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.exists_total_of_boundaryNullRel := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.exists_total_of_boundaryNullRel

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.output_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.output_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.rel_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.rel_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberExactness.exists_connecting_of_nullRel := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberExactness.exists_connecting_of_nullRel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberExactness.exists_connecting_of_nullRel_all := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberExactness.exists_connecting_of_nullRel_all

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TotalExactness.exists_fiber_of_baseNullRel := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.TotalExactness.exists_fiber_of_baseNullRel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TotalExactness.exists_fiber_of_baseNullRel_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.TotalExactness.exists_fiber_of_baseNullRel_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.face._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BaseExactness.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BaseExactness.face.eq_1
