module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicPresentation

/-!
概要：各次数の全射の圏を有限順序関手で再添字付けする。
方針：Hom圏への全関手の前合成を使う。
規約：単位と全水平合成を保つ実関手を構成する。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限順序関手による全次数の実射の再添字付け。
方針：元の実関手へ前合成する。規約：同じ二対象を保持する。
使われ方：Riehl–Verity Definition 2.1.4 の単体作用。 -/
def walkingAdjunctionLevelReindex {m n : ℕ} (P : Fin (m + 1) ⥤ Fin (n + 1)) :
    WalkingAdjunctionLevel n ⥤ WalkingAdjunctionLevel m where
  obj X := ⟨X.point⟩
  map F := P ⋙ F
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：恒等順序関手での再添字付けは全恒等関手。
方針：前合成の恒等則を使う。規約：対象と全射を保持する。
使われ方：Riehl–Verity Definition 2.1.4 の全単体作用。 -/
lemma walkingAdjunctionLevelReindex_id (n : ℕ) :
    walkingAdjunctionLevelReindex (𝟭 (Fin (n + 1))) = 𝟭 (WalkingAdjunctionLevel n) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y F
  exact heq_of_eq (CategoryTheory.Functor.id_comp F)

/-- 概要：再添字付けの合成は元の順序関手の合成と一致する。
方針：前合成の結合則を使う。規約：反変の順序を明示する。
使われ方：Riehl–Verity Definition 2.1.4 の全単体作用。 -/
lemma walkingAdjunctionLevelReindex_comp {l m n : ℕ}
    (P : Fin (m + 1) ⥤ Fin (n + 1)) (Q : Fin (l + 1) ⥤ Fin (m + 1)) :
    walkingAdjunctionLevelReindex P ⋙ walkingAdjunctionLevelReindex Q =
      walkingAdjunctionLevelReindex (Q ⋙ P) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y F
  exact heq_of_eq (CategoryTheory.Functor.assoc Q P F).symm

/-- 概要：長さ0の全単体は再添字付けても長さ0。
方針：各頂点の長さ0を回収して有限和へ戻す。
規約：任意の有限順序関手。使われ方：Riehl–Verity Proposition 3.1.10 の単位の検出。 -/
lemma walkingAdjunctionLevelSize_precomp_zero {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (P : Fin (m + 1) ⥤ Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (h : walkingAdjunctionLevelSize F = 0) : walkingAdjunctionLevelSize (P ⋙ F) = 0 := by
  unfold walkingAdjunctionLevelSize
  apply Finset.sum_eq_zero
  intro i hi
  exact walkingAdjunctionLevelSize_vertex_zero F h (P.obj i)

end SerrePositivity.InfinityCategories.HA.Monads
