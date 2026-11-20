module


public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：filtered colimit の境界定数単体とホモトピー関係の有限段での実現。
方針：有限な境界条件と RelStruct の面の等式を相対因子分解で同時に移す。
規約：ここでの因子分解は Kan 性を必要としない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の π_* と余極限の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

include hc in
/-- 概要：余極限の境界定数単体は指定した基点の段より後で実現できる。
方針：境界包含に対する相対因子分解を使う。
規約：零次単体も含む。返す等式は代表の基礎射の等式。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の余極限比較の全射性。 -/
theorem ptSimplex_filtered_factorization (j : J) (x : (F.obj j) _⦋0⦌) (n : ℕ)
    (s : c.pt.PtSimplex n ((c.ι.app j).app _ x)) :
    ∃ (k : J) (v : j ⟶ k) (t : (F.obj k).PtSimplex n ((F.map v).app _ x)),
      t.map ≫ c.ι.app k = s.map := by
  have hs : (boundary n).ι ≫ s.map = SSet.const ((c.ι.app j).app _ x) := by
    exact s.comp_map_eq_const (boundary n).ι
  have h : SSet.const (X := (∂Δ[n] : SSet.{u})) x ≫ c.ι.app j =
      (boundary n).ι ≫ s.map := by rw [SSet.const_comp, hs]
  obtain ⟨k, v, q, hq, heq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.finite_relative_factorization hc (boundary n).ι j
    (SSet.const x) s.map h
  refine ⟨k, v, { map := q, comm := ?_ }, heq⟩
  rw [SSet.const_comp]
  change (boundary n).ι ≫ q = SSet.const ((F.map v).app _ x)
  simpa only [SSet.const_comp] using hq

include hc in
/-- 概要：同じ段の境界定数単体が余極限で一致すれば一つの後続段で一致する。
方針：標準単体の有限表示性で基礎射の等式を後続段へ移す。
規約：基点は遷移射で運ぶ。
使われ方：Goerss–Jardine I §7、HA §1.4.2。代表の比較。 -/
theorem ptSimplex_filtered_eq (j : J) {x : (F.obj j) _⦋0⦌} {n : ℕ}
    (s t : (F.obj j).PtSimplex n x) (h : s.map ≫ c.ι.app j = t.map ≫ c.ι.app j) :
    ∃ (k : J) (v : j ⟶ k),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (F.map v) rfl s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (F.map v) rfl t := by
  obtain ⟨k, v, hv⟩ := Limits.exists_eq_of_preservesColimit_coyoneda_self hc s.map t.map h
  refine ⟨k, v, ?_⟩
  apply RelativeMorphism.ext
  exact hv

include hc in
/-- 概要：余極限での RelStruct は元の二つの代表を保って後続段で実現できる。
方針：隣接二面と残りの定数面の有限個の等式を同時に因子分解する。
規約：零次数を含み、面の添字 i は任意。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の余極限比較の単射性。 -/
theorem relStruct_filtered_factorization (j : J) {x : (F.obj j) _⦋0⦌} {n : ℕ}
    (s t : (F.obj j).PtSimplex n x) (i : Fin (n + 1))
    (r : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (c.ι.app j) rfl s)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (c.ι.app j) rfl t) i) :
    ∃ (k : J) (v : j ⟶ k),
      Nonempty (PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (F.map v) rfl s)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (F.map v) rfl t) i) := by
  have hcast : i.castSucc.val = i.val := rfl
  have hsucc : i.succ.val = i.val + 1 := rfl
  let faces (a : Fin (n + 2)) : (Δ[n] : SSet.{u}) ⟶ F.obj j :=
    if a = i.castSucc then s.map else if a = i.succ then t.map else SSet.const x
  have hfaces (a : Fin (n + 2)) : faces a ≫ c.ι.app j = stdSimplex.δ a ≫ r.map := by
    by_cases ha : a = i.castSucc
    · subst a
      simp [faces, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
    · by_cases hb : a = i.succ
      · subst a
        simp [faces, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
      · have hlt : a < i.castSucc ∨ i.succ < a := by omega
        rcases hlt with hlt | hgt
        · simp [faces, ha, hb, r.δ_map_of_lt a hlt]
        · simp [faces, ha, hb, r.δ_map_of_gt a hgt]
  obtain ⟨k, v, q, hq, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.finite_equations_factorization hc
    (fun a : Fin (n + 2) ↦ stdSimplex.δ a) j faces r.map hfaces
  refine ⟨k, v, ⟨{
    map := q
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · simpa [faces, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex] using hq i.castSucc
  · have hi : i.succ ≠ i.castSucc := by omega
    simpa [faces, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex] using hq i.succ
  · intro a ha
    have h₁ : a ≠ i.castSucc := by omega
    have h₂ : a ≠ i.succ := by omega
    simpa [faces, h₁, h₂] using hq a
  · intro a ha
    have h₁ : a ≠ i.castSucc := by omega
    have h₂ : a ≠ i.succ := by omega
    simpa [faces, h₁, h₂] using hq a

variable [∀ j, KanComplex (F.obj j)] [KanComplex c.pt]

include hc in
/-- 概要：filtered colimit のホモトピー類は指定した基点の段の後続段から来る。
方針：代表単体を相対因子分解し、基点の像を cocone の自然性で合わせる。
規約：全自然数次数で有効。基点保存式も存在の出力に含める。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_* と余極限の比較の全射性。 -/
theorem homotopy_filtered_surjective (j : J) (x : (F.obj j) _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy c.pt n ((c.ι.app j).app _ x)) :
    ∃ (k : J) (v : j ⟶ k)
      (hb : (c.ι.app k).app _ ((F.map v).app _ x) = (c.ι.app j).app _ x)
      (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (F.obj k) n ((F.map v).app _ x)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (Y := c.pt) n (c.ι.app k) hb b = a := by
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  obtain ⟨k, v, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ptSimplex_filtered_factorization hc j x n s
  have hb : (c.ι.app k).app _ ((F.map v).app _ x) = (c.ι.app j).app _ x :=
    congrArg (fun z : F.obj j ⟶ c.pt ↦ z.app _ x) (c.w v)
  refine ⟨k, v, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n t, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  congr 1
  apply RelativeMorphism.ext
  exact ht

include hc in
/-- 概要：同じ段のホモトピー類が余極限で一致すれば後続段で一致する。
方針：代表単体の等式を一本の RelStruct で表し、その全ての面を後続段で実現する。
規約：零次数を含む。単射な遷移射は不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_* と余極限の比較の単射性。 -/
theorem homotopy_filtered_eq_eventually (j : J) {x : (F.obj j) _⦋0⦌} (n : ℕ)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (F.obj j) n x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (Y := c.pt) n (c.ι.app j) rfl a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (Y := c.pt) n (c.ι.app j) rfl b) :
    ∃ (k : J) (v : j ⟶ k),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (F.map v) rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (F.map v) rfl b := by
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n b
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk] at h
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ 0).1 h
  obtain ⟨k, v, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.relStruct_filtered_factorization hc j s t 0 r
  refine ⟨k, v, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ 0).2 hr

end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
