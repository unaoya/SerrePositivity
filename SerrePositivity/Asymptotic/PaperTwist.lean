module

public import SerrePositivity.Asymptotic.BaseChangeIdentity
public import Mathlib.Algebra.Algebra.Hom

/-! # 論文の支持圏のひねりと K₀ 上の群作用

行列の係数変更に由来する関手を、固定したパラメータの支持圏の自己関手にする。
作用は自己同型に沿った係数拡大であり、K₀ 上では左作用となる。
有限複体の係数制限による `twist` とは逆元の規約が異なる。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S V : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  [CommRing V] [Nontrivial V] {s : ℕ → ℕ} {e : ℕ}

/-- 係数変更先のパラメータを指定した、論文の支持圏の係数変更。 -/
noncomputable def paperSupportedChangeRingTo (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤
      (paperSupportedRank (s := s) w).FullSubcategory := by
  subst w
  exact paperSupportedChangeRing φ z

noncomputable instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedChangeRingTo (s := s) φ z w h).CommShift ℤ := by
  subst w
  dsimp [paperSupportedChangeRingTo]
  infer_instance

instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedChangeRingTo (s := s) φ z w h).IsTriangulated := by
  subst w
  dsimp [paperSupportedChangeRingTo]
  infer_instance

/-- パラメータを指定した係数変更の K₀ 写像。 -/
noncomputable def paperSupportedMap (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+
      TriangulatedK0 (paperSupportedRank (s := s) w).FullSubcategory :=
  TriangulatedK0.map (paperSupportedChangeRingTo φ z w h)

/-- 同じ環準同型による写像は、パラメータの等式の証明によらず一致する。 -/
lemma paperSupportedMap_congr (φ ψ : R →+* S) (z : Fin e → R) (w : Fin e → S)
    (h : φ ∘ z = w) (k : ψ ∘ z = w) (hφ : φ = ψ) :
    paperSupportedMap (s := s) φ z w h = paperSupportedMap ψ z w k := by
  subst ψ
  rfl

/-- 指定したパラメータに関しても係数変更の合成則が成り立つ。 -/
lemma paperSupportedMap_comp (φ : R →+* S) (ψ : S →+* V)
    (z : Fin e → R) (w : Fin e → S) (v : Fin e → V)
    (h : φ ∘ z = w) (k : ψ ∘ w = v) :
    (paperSupportedMap (s := s) ψ w v k).comp (paperSupportedMap φ z w h) =
      paperSupportedMap (ψ.comp φ) z v (by rw [← k, ← h]; rfl) := by
  subst w v
  exact paperSupportedChangeRingK0_comp φ z ψ

/-- 恒等写像は支持つき K₀ の恒等写像を誘導する。 -/
lemma paperSupportedMap_id (z : Fin e → R) :
    paperSupportedMap (s := s) (RingHom.id R) z z rfl = AddMonoidHom.id _ :=
  paperSupportedChangeRingK0_id z

variable {A T : Type u} [CommRing A] [CommRing T] [Nontrivial T] [Algebra A T]
  (z : Fin e → A) {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

omit [Nontrivial T] in
/-- A 上の作用は A のパラメータの像を固定する。 -/
lemma paperTwist_parameters (g : G) :
    (MulSemiringAction.toAlgHom A T g).toRingHom ∘ (algebraMap A T ∘ z) =
      algebraMap A T ∘ z :=
  funext fun j ↦ (MulSemiringAction.toAlgHom A T g).commutes (z j)

/-- 自己同型に沿った係数拡大による、論文の支持圏のひねり。 -/
noncomputable abbrev paperTwist (g : G) :
    (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory ⥤
      (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory :=
  paperSupportedChangeRingTo (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (paperTwist_parameters z g)

/-- ひねりが K₀ に誘導する準同型。 -/
noncomputable abbrev paperTwistK0 (g : G) :
    TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory →+
      TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory :=
  TriangulatedK0.map (paperTwist (T := T) z g)

/-- 単位元によるひねりは K₀ 上で恒等写像。 -/
lemma paperTwistK0_one :
    paperTwistK0 (s := s) (T := T) z (1 : G) = AddMonoidHom.id _ := by
  have h : (MulSemiringAction.toAlgHom A T (1 : G)).toRingHom = RingHom.id T :=
    RingHom.ext (one_smul G)
  change paperSupportedMap _ _ _ _ = _
  simp only [h]
  exact paperSupportedMap_id _

/-- 係数拡大によるひねりは K₀ 上で左作用の合成則を満たす。 -/
lemma paperTwistK0_mul (g h : G) :
    paperTwistK0 (s := s) (T := T) z (g * h) =
      (paperTwistK0 (s := s) (T := T) z g).comp (paperTwistK0 (s := s) (T := T) z h) := by
  have hh : (MulSemiringAction.toAlgHom A T (g * h)).toRingHom =
      (MulSemiringAction.toAlgHom A T g).toRingHom.comp
        (MulSemiringAction.toAlgHom A T h).toRingHom :=
    RingHom.ext (mul_smul g h)
  have hc := paperSupportedMap_comp (s := s)
    (MulSemiringAction.toAlgHom A T h).toRingHom
    (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (algebraMap A T ∘ z)
    (paperTwist_parameters z h) (paperTwist_parameters z g)
  change paperSupportedMap (MulSemiringAction.toAlgHom A T (g * h)).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) _ = _
  exact (paperSupportedMap_congr _ _ _ _ _ _ hh).trans hc.symm

set_option maxHeartbeats 800000 in
-- 支持部分圏と商の型に沿った群作用の比較に必要。
/-- 実際の係数変更から得られる、支持つき K₀ 上の群作用。 -/
noncomputable instance paperK0DistribMulAction :
    DistribMulAction G
      (TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) where
  smul g := paperTwistK0 (s := s) (T := T) z g
  one_smul x := by
    change paperTwistK0 (s := s) (T := T) z (1 : G) x = x
    exact DFunLike.congr_fun (paperTwistK0_one (s := s) (T := T) (G := G) z) x
  mul_smul g h x := by
    change paperTwistK0 (s := s) (T := T) z (g * h) x =
      paperTwistK0 (s := s) (T := T) z g (paperTwistK0 (s := s) (T := T) z h x)
    exact DFunLike.congr_fun (paperTwistK0_mul (s := s) (T := T) z g h) x
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

/-- 対象の類への作用は、その対象をひねった類である。 -/
lemma paperK0_smul_mk (g : G)
    (X : (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    g • TriangulatedK0.mk X = TriangulatedK0.mk ((paperTwist (T := T) z g).obj X) :=
  TriangulatedK0.map_mk _ _

end SerrePositivity.Asymptotic
