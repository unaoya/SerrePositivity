module

public import SerrePositivity.InfinityCategories.F2.IntervalShapeContraction

/-!
概要：path の形状収縮の始点と終点を、時刻を動かしたまま計算する。
方針：二点鎖の収縮を頂点列ごとに計算する。
規約：全時刻の式。使われ方：区間置換の定値切断から恒等射への指定円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 形状の始点は、収縮の全時刻で始点に固定される。 -/
lemma intervalShapeContraction_path_zero (T : SSet.{u}) :
    prismEndpoint 0 (T ⊗ (Δ[1] : SSet.{u})) ≫ intervalShapeContraction T =
      fst T (Δ[1] : SSet.{u}) ≫ prismEndpoint 0 T := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    change (if (stdSimplex.objEquiv s).toOrderHom i = 0 then (0 : Fin 2) else 0) = 0
    simp only [ite_self]
  · rfl

/-- 形状の終点は、収縮の時刻をそのまま読み出す。 -/
lemma intervalShapeContraction_path_one (T : SSet.{u}) :
    prismEndpoint 1 (T ⊗ (Δ[1] : SSet.{u})) ≫ intervalShapeContraction T =
      (β_ T (Δ[1] : SSet.{u})).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    let t : Fin 2 := (stdSimplex.objEquiv s).toOrderHom i
    change (if t = 0 then (0 : Fin 2) else 1) = t
    split_ifs with h
    · exact h.symm
    · have ht : t.val < 2 := t.isLt
      have hz : t.val ≠ 0 := fun h₀ => h (Fin.ext h₀)
      apply Fin.ext
      change 1 = t.val
      omega
  · rfl

end SerrePositivity.InfinityCategories.F2
