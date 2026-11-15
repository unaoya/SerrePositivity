module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutFibers

/-!
概要：切断を持つ有限順序関手での再添字付けは原子性を保つ。
方針：実水平分解を切断へ戻し、同じ像の頂点での長さの一致で単位を検出する。
規約：切断は実際の順序関手として指定し、原子性の保存を仮定しない。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：再添字付けの実分解の左因子は、切断上で長さ0なら全体で長さ0。
方針：各頂点を切断上の同じ像の頂点と比較する。
規約：左因子の単位性を仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.left_size_zero_of_section_zero {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1))) (a : WalkingAdjunctionFactorization (P ⋙ F))
    (ha : walkingAdjunctionLevelSize (Q ⋙ a.left) = 0) : walkingAdjunctionLevelSize a.left = 0 := by
  unfold walkingAdjunctionLevelSize
  apply Finset.sum_eq_zero
  intro i hi
  have hP : P.obj i = P.obj (Q.obj (P.obj i)) :=
    (CategoryTheory.Functor.congr_obj hQP (P.obj i)).symm
  have hf := a.left_length_eq_of_reindex_fiber P F hP
  have hs := walkingAdjunctionLevelSize_vertex_zero (Q ⋙ a.left) ha (P.obj i)
  exact hf.trans hs

/-- 概要：再添字付けの実分解の右因子も、切断上で長さ0なら全体で長さ0。
方針：同じ像の頂点での右因子の長さの一致を使う。
規約：全ての頂点を回収する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.right_size_zero_of_section_zero {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1))) (a : WalkingAdjunctionFactorization (P ⋙ F))
    (ha : walkingAdjunctionLevelSize (Q ⋙ a.right) = 0) :
    walkingAdjunctionLevelSize a.right = 0 := by
  unfold walkingAdjunctionLevelSize
  apply Finset.sum_eq_zero
  intro i hi
  have hP : P.obj i = P.obj (Q.obj (P.obj i)) :=
    (CategoryTheory.Functor.congr_obj hQP (P.obj i)).symm
  have hf := a.right_length_eq_of_reindex_fiber P F hP
  have hs := walkingAdjunctionLevelSize_vertex_zero (Q ⋙ a.right) ha (P.obj i)
  exact hf.trans hs

/-- 概要：切断を持つ有限順序関手による再添字付けは原子的な実射を保つ。
方針：分解を切断へ戻し、元の原子性と切断上の長さ0の検出を使う。
規約：原子性の保存は結論として証明する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionLevelIsAtomic_precomp_of_split {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1)))
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) (P ⋙ F) := by
  have hret : Q ⋙ (P ⋙ F) = F := by
    change (Q ⋙ P) ⋙ F = F
    rw [hQP, CategoryTheory.Functor.id_comp]
  constructor
  · by_contra hpos
    have hz : walkingAdjunctionLevelSize (P ⋙ F) = 0 := by omega
    have hs := walkingAdjunctionLevelSize_precomp_zero Q (P ⋙ F) hz
    have he := congrArg (fun K : Fin (n + 1) ⥤ walkingAdjunctionHom X Y =>
      walkingAdjunctionLevelSize K) hret
    have hp := hf.1
    omega
  · intro Z A B hab
    let a : WalkingAdjunctionFactorization (P ⋙ F) := ⟨Z.point, A, B, hab⟩
    have hs : (Q ⋙ A).prod' (Q ⋙ B) ⋙ walkingAdjunctionHorizontal X Z.point Y = F := by
      calc
        _ = Q ⋙ (A.prod' B ⋙ walkingAdjunctionHorizontal X Z.point Y) := rfl
        _ = Q ⋙ (P ⋙ F) := congrArg (fun K => Q ⋙ K) hab
        _ = F := hret
    rcases hf.2 ⟨Z.point⟩ (Q ⋙ A) (Q ⋙ B) hs with hA | hB
    · exact Or.inl
        (WalkingAdjunctionFactorization.left_size_zero_of_section_zero P Q F hQP a hA)
    · exact Or.inr
        (WalkingAdjunctionFactorization.right_size_zero_of_section_zero P Q F hQP a hB)

end SerrePositivity.InfinityCategories.HA.Monads
