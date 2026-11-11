module

public import SerrePositivity.AlgebraicGeometry.DeterminantalCenterBaseChange
public import SerrePositivity.AlgebraicGeometry.DeterminantalCenterSplitLine
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Ideal.Prod

/-!
概要：有限自由代数が底変換後に階数一因子を持つとき、基底側にその因子の中心を含む中心を作る。
方針：元のイデアルの行列式中心を作り、底変換後に直積の座標で行列式を分ける。
規約：基底環を Noether とし、境界元の冪が元のイデアルに入る場合を扱う。
使われ方：Stacks 0813 で標準 étale の対角成分に中心を降下する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem determinantalCenter_le_of_range_le
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ}
    (f : M →ₗ[R] (Fin n → R)) (g : N →ₗ[R] (Fin n → R))
    (h : LinearMap.range f ≤ LinearMap.range g) :
    determinantalCenter f ≤ determinantalCenter g := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v, rfl⟩
  have hx (j : Fin n) : ∃ w, g w = f (v j) := h (LinearMap.mem_range_self _ _)
  choose w hw using hx
  have heq : imageColumnMatrix f v = imageColumnMatrix g w := by
    ext i j
    exact (congrFun (hw j) i).symm
  change (imageColumnMatrix f v).det ∈ _
  rw [heq]
  exact (determinantalCenterGenerator g w).property

/--
概要：有限自由代数の底変換の階数一因子に落ちるイデアルを因子として含む、
基底環上の有限生成中心が存在する。元のイデアルが含む境界元の冪から、中心の境界冪も得られる。
方針：底変換したイデアルを直積へ移して二つのイデアルに分け、行列式中心を積に分ける。
規約：第二因子も有限自由で、階数零を許す。
使われ方：標準 étale の有限自由なモニック模型から中心を降下する。
-/
theorem exists_center_factor_of_split_finiteFree
    {R B C D : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Nontrivial B]
    [CommRing C] [CommRing D] [Algebra R B] [Algebra R C] [Algebra B D] {n m : ℕ}
    (b : Module.Basis (Fin n) R C) (d : Module.Basis (Fin m) B D)
    (e : B ⊗[R] C ≃ₐ[B] B × D) (P : Ideal C) (a : R) (k : ℕ)
    (ha : algebraMap R C (a ^ k) ∈ P) :
    ∃ I : Ideal R, I.FG ∧ a ^ (k * n) ∈ I ∧ ∃ J' : Ideal B,
      I.map (algebraMap R B) =
        P.map ((RingHom.fst B D).comp
          (e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R)).toRingHom)) * J' := by
  classical
  let : Module.Finite R C := Module.Finite.of_basis b
  let : Module.Finite B D := Module.Finite.of_basis d
  let : Module.Free B D := Module.Free.of_basis d
  have hn : n = m + 1 := by
    calc
      n = Module.finrank B (B ⊗[R] C) := by
        rw [Module.finrank_eq_card_basis (b.baseChange B), Fintype.card_fin]
      _ = Module.finrank B (B × D) := e.toLinearEquiv.finrank_eq
      _ = m + 1 := by
        rw [Module.finrank_prod, Module.finrank_self, Module.finrank_eq_card_basis d,
          Fintype.card_fin, Nat.add_comm]
  subst n
  let P₀ := P.restrictScalars R
  let f := b.equivFun.toLinearMap.comp P₀.subtype
  let I := determinantalCenter f
  let H : (Fin (m + 1) → R) →ₗ[R] P₀ :=
    ((a ^ k) • b.equivFun.symm.toLinearMap).codRestrict _ fun x => by
      change (a ^ k) • b.equivFun.symm x ∈ P
      rw [Algebra.smul_def]
      exact P.mul_mem_right _ ha
  have hH : f.comp H = (a ^ k) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change b.equivFun ((a ^ k) • b.equivFun.symm x) = (a ^ k) • x
    rw [map_smul, LinearEquiv.apply_symm_apply]
  let K := P.map (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom
  let L := K.map e.toRingHom
  let J := L.map (RingHom.fst B D)
  let T := L.map (RingHom.snd B D)
  have hK : P₀.baseChange B = K.restrictScalars B := by
    ext x
    exact (SetLike.ext_iff.mp (Ideal.map_includeRight_eq (R := R) (A := B) P) x).symm
  have hL : L = J.prod T := Ideal.ideal_prod_eq L
  let c := Fin.consLinearEquiv B (fun _ : Fin (m + 1) => B)
  let u := LinearEquiv.prodCongr (LinearEquiv.refl B B) d.equivFun
  let b' := (b.baseChange B).equivFun
  let F := e.toLinearEquiv.trans (u.trans c)
  let g := F.toLinearMap.comp (K.restrictScalars B).subtype
  let t := d.equivFun.toLinearMap.comp (T.restrictScalars B).subtype
  let g' := c.toLinearMap.comp (J.subtype.prodMap t)
  have hcoord : ((b'.symm.trans F).toLinearMap.comp
      (b'.toLinearMap.comp (K.restrictScalars B).subtype)) = g := by
    apply LinearMap.ext
    intro x
    change F (b'.symm (b' x.1)) = F x.1
    rw [b'.symm_apply_apply]
  have hrange : LinearMap.range g = LinearMap.range g' := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : e y.1 ∈ J.prod T := hL ▸ Ideal.mem_map_of_mem e.toRingHom y.2
      exact ⟨(⟨(e y.1).1, hy.1⟩, ⟨(e y.1).2, hy.2⟩), rfl⟩
    · rintro ⟨y, rfl⟩
      have hy : ((y.1 : B), (y.2 : D)) ∈ L := hL.symm ▸ And.intro y.1.2 y.2.2
      obtain ⟨z, hz, he⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hy
      refine ⟨⟨z, hz⟩, ?_⟩
      change c (u (e z)) = c (u ((y.1 : B), (y.2 : D)))
      exact congrArg (fun p => c (u p)) he
  have hpow : a ^ (k * (m + 1)) ∈ I := by
    simpa only [Fintype.card_fin] using boundary_pow_mem_determinantalCenter f H a k hH
  refine ⟨I, IsNoetherian.noetherian _, hpow, determinantalCenter t, ?_⟩
  have hJ : J = P.map ((RingHom.fst B D).comp
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R)).toRingHom)) := by
    simp only [J, L, K, Ideal.map_map, RingHom.comp_assoc]
  rw [← hJ]
  change I.map (algebraMap R B) = J * determinantalCenter t
  rw [show I.map (algebraMap R B) = determinantalCenter
      (b'.toLinearMap.comp (K.restrictScalars B).subtype) by
      exact (determinantalCenter_submodule_baseChange b P₀ (IsNoetherian.noetherian _)).trans
        (by rw [hK]),
    ← determinantalCenter_postcomp_linearEquiv _ (b'.symm.trans F), hcoord,
    le_antisymm (determinantalCenter_le_of_range_le g g' hrange.le)
      (determinantalCenter_le_of_range_le g' g hrange.ge)]
  exact determinantalCenter_prod_line J t

end SerrePositivity.AlgebraicGeometry
