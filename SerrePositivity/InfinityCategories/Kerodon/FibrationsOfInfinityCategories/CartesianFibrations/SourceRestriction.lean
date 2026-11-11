module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRightRestriction

/-!
概要：始点の標準零単体への相対 coslice 制限による cocartesian 辺の判定。
方針：一次の初期ホーンと始点の面を同一視し、表示同型を移す。
規約：始点包含は δ₁ : Δ[0] → Δ[1]。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、Proposition 5.2.5.1（Tag 01VU） の三角形の貼り合わせ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：一次の初期ホーンは終点を除く面。
方針：ホーンの面による上限表示で唯一の面を取り出す。
規約：初期ホーンは horn 1 0。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、始点包含の表示変更。 -/
lemma initialHorn_eq_sourceFace :
    horn.{u} 1 0 = stdSimplex.face {(1 : Fin 2)}ᶜ := by
  apply le_antisymm
  · rw [horn_eq_iSup]
    apply iSup_le
    intro j
    have hj : j.val = 1 := by
      rcases j with ⟨j, hj⟩
      change j ≠ (0 : Fin 2) at hj
      fin_cases j
      · exact False.elim (hj rfl)
      · rfl
    simp only [hj, le_refl]
  · exact face_le_horn 1 0 (by decide)

/-- 概要：cocartesian 辺の始点への相対 coslice 制限は trivial Kan fibration。
方針：初期ホーンでの判定を標準零単体の表示同型に移す。
規約：射 q に inner fibration 性を仮定しない。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、合成の三角形の始点の錐。 -/
lemma relativeCosliceRestriction_source_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction e q (stdSimplex.δ (1 : Fin 2))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge e q he
  rw [initialHorn_eq_sourceFace] at h
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_trivialKanFibration_subcomplexIso e q
    (stdSimplex.face {(1 : Fin 2)}ᶜ) (stdSimplex.faceSingletonComplIso (1 : Fin 2))
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using hh

/-- 概要：始点への相対 coslice 制限の充填性から辺の cocartesian 性を得る。
方針：標準零単体の逆表示への制限を合成して初期ホーンの判定へ戻す。
規約：対象・底の quasicategory 性を追加で仮定しない。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、三角形の長辺の判定。 -/
lemma isCocartesianEdge_of_relativeCosliceRestriction_source {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction e q (stdSimplex.δ (1 : Fin 2)))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv e) := by
  let iso := stdSimplex.faceSingletonComplIso.{u} (1 : Fin 2)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_trivialKanFibration_comp e q
    (stdSimplex.δ (1 : Fin 2)) iso.inv
  have hd : iso.inv ≫ stdSimplex.δ (1 : Fin 2) =
      (stdSimplex.face {(1 : Fin 2)}ᶜ).ι := by
    rw [← stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin 2)]
    simp only [iso, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hd] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_subcomplex, ← initialHorn_eq_sourceFace] at h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_relativeCosliceMap_trivialKanFibration e q h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
