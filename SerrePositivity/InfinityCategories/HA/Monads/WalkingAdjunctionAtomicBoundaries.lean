module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutFactorization
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicWords

/-!
概要：原子的な全単体の分解を左右の単位分解の二つに照合する。
方針：長さ0の因子を元の実分解の一意性で単位分解へ戻す。
規約：実関手の全射と合成の証明を含む実分解の等式を使う。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の切れ目の判定。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：左因子の長さ0は実分解が左の単位分解であることと同値。
方針：全頂点の長さ0と左因子の長さによる一意性を使う。
規約：中点の一致も結論に含む。使われ方：Riehl–Verity §4.1の原子の境界。 -/
lemma WalkingAdjunctionFactorization.left_size_zero_iff
    (a : WalkingAdjunctionFactorization H) : walkingAdjunctionLevelSize a.left = 0 ↔
      a = walkingAdjunctionSourceFactorization H := by
  constructor
  · intro hz
    apply a.ext_prefix_length (walkingAdjunctionSourceFactorization H)
    intro i
    exact (walkingAdjunctionLevelSize_vertex_zero a.left hz i).trans
      (walkingAdjunctionVertexLength_id X).symm
  · intro he
    subst a
    exact walkingAdjunctionLevelSize_id n X

/-- 概要：右因子の長さ0は実分解が右の単位分解であることと同値。
方針：全長の加法則から左因子の長さを回収して実分解の一意性を使う。
規約：左右の全関手を回収する。使われ方：Riehl–Verity §4.1の原子の境界。 -/
lemma WalkingAdjunctionFactorization.right_size_zero_iff
    (a : WalkingAdjunctionFactorization H) : walkingAdjunctionLevelSize a.right = 0 ↔
      a = walkingAdjunctionTargetFactorization H := by
  constructor
  · intro hz
    apply a.ext_prefix_length (walkingAdjunctionTargetFactorization H)
    intro i
    have hr := walkingAdjunctionLevelSize_vertex_zero a.right hz i
    have he := CategoryTheory.Functor.congr_obj a.fac i
    have hl := walkingAdjunctionVertexLength_comp X a.middle Y (a.left.obj i) (a.right.obj i)
    change (walkingAdjunctionHorizontal X a.middle Y).obj (a.left.obj i, a.right.obj i) =
      H.obj i at he
    rw [he, hr] at hl
    simp only [Nat.add_zero] at hl
    exact hl.symm
  · intro he
    subst a
    exact walkingAdjunctionLevelSize_id n Y

/-- 概要：原子的な全単体では実分解は左右の単位分解だけであり逆も成り立つ。
方針：元の原子性の長さ0の条件を、実分解の等式へ両方向に移す。
規約：長さが正である条件を保持する。使われ方：Riehl–Verity §4.1の原子の判定。 -/
lemma walkingAdjunctionLevelIsAtomic_iff_boundary_factorizations
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      0 < walkingAdjunctionLevelSize H ∧ ∀ a : WalkingAdjunctionFactorization H,
        a = walkingAdjunctionSourceFactorization H ∨
          a = walkingAdjunctionTargetFactorization H := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a
    rcases h.2 ⟨a.middle⟩ a.left a.right a.fac with hl | hr
    · exact Or.inl (a.left_size_zero_iff.mp hl)
    · exact Or.inr (a.right_size_zero_iff.mp hr)
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro Z A B hab
    let a : WalkingAdjunctionFactorization H := ⟨Z.point, A, B, hab⟩
    rcases h a with hl | hr
    · exact Or.inl (a.left_size_zero_iff.mpr hl)
    · exact Or.inr (a.right_size_zero_iff.mpr hr)

end SerrePositivity.InfinityCategories.HA.Monads
