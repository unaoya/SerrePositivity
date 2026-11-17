module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicPaths
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualFactorization

/-!
概要：同じ全単体の原子的な左因子と、その残りは一意である。
方針：実細分の残りが原子性で単位となることを使う。
規約：全次数の実関手の等式として回収する。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：原子的な二つの左因子の間の実細分は単位であり、両分解は一致する。
方針：原子性・長さ0の単位の検出・全単位則を使う。
規約：細分の実関手から等式を回収する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.eq_of_atomic_refinement
    (a b : WalkingAdjunctionFactorization H)
    (T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨a.middle⟩) a.left)
    (hb : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨b.middle⟩) b.left)
    (hp : a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left)
    (hq : T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) : a = b := by
  have ht : walkingAdjunctionLevelSize T = 0 :=
    (hb.2 ⟨a.middle⟩ a.left T hp).resolve_left (Nat.ne_of_gt ha.1)
  have hM := walkingAdjunctionLevelSize_zero_endpoints T ht
  rcases a with ⟨M, L, R, hL⟩
  rcases b with ⟨N, L', R', hR⟩
  change M = N at hM
  subst N
  have hT := walkingAdjunctionLevelSize_zero_eq_id T ht
  subst T
  change L.prod' ((Functor.const _).obj (walkingAdjunctionIdentity M)) ⋙
    walkingAdjunctionHorizontal X M M = L' at hp
  change ((Functor.const _).obj (walkingAdjunctionIdentity M)).prod' R' ⋙
    walkingAdjunctionHorizontal M M Y = R at hq
  rw [walkingAdjunctionHorizontal_rightUnit] at hp
  rw [walkingAdjunctionHorizontal_leftUnit] at hq
  subst L'
  subst R'
  rfl

/-- 概要：同じ全単体の原子的な左因子を持つ二分解は一致する。
方針：構成済みの実細分の二つの場合に、原子性の単位の検出を適用する。
規約：全射を含む分解の等式。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.eq_of_atomic_left (a b : WalkingAdjunctionFactorization H)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨a.middle⟩) a.left)
    (hb : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨b.middle⟩) b.left) : a = b := by
  rcases a.exists_refinement b with ⟨T, hp, hq⟩ | ⟨T, hp, hq⟩
  · exact a.eq_of_atomic_refinement b T ha hb hp hq
  · exact (b.eq_of_atomic_refinement a T hb ha hp hq).symm

/-- 概要：原子的な先頭の二射の合成が等しければ、先頭と残りをともに回収できる。
方針：同じ実単体の二分解の等式を各欄へ射影する。
規約：中間の対象と射の異種等式を明示する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionAtomicLeftCancellation {A B C D : WalkingAdjunctionLevel n}
    (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (hf : WalkingAdjunctionLevelIsAtomic f) (hg : WalkingAdjunctionLevelIsAtomic g)
    (h : f ≫ u = g ≫ v) : ∃ _hBC : B = C, HEq f g ∧ HEq u v := by
  let K : Fin (n + 1) ⥤ walkingAdjunctionHom A.point D.point := f ≫ u
  let a : WalkingAdjunctionFactorization K := ⟨B.point, f, u, rfl⟩
  let b : WalkingAdjunctionFactorization K := ⟨C.point, g, v, h.symm⟩
  have he := a.eq_of_atomic_left b hf hg
  have hBC : B = C := by
    have hp := congrArg WalkingAdjunctionFactorization.middle he
    change B.point = C.point at hp
    cases B
    cases C
    cases hp
    rfl
  have hl : ∀ {a b : WalkingAdjunctionFactorization K}, a = b → HEq a.left b.left := by
    intro a b h
    cases h
    rfl
  have hr : ∀ {a b : WalkingAdjunctionFactorization K}, a = b → HEq a.right b.right := by
    intro a b h
    cases h
    rfl
  exact ⟨hBC, hl he, hr he⟩

end SerrePositivity.InfinityCategories.HA.Monads
