module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # 二項直和から出る Hom の全次数座標

概要：二項直和から出る cochain は二つの包含での成分と線形に同値であり、微分と両立する。
方針：射影による二つの前合成の和を逆写像とし、二項直和の恒等射の分解を使う。
規約：次数の制限はない。使われ方：D7 の cofiber の未知成分の明示解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] (B C X : Complex S)

/-- 概要：直和から出る Hom の全次数の線形座標。
方針：二包含での成分と二射影による和を互いに逆とする。
規約：任意の非有界複体。使われ方：B・C 側の右辺の合成。 -/
def biproductFromHomCoordinates (n : ℤ) :
    Cochain (B ⊞ C) X n ≃ₗ[S] (Cochain B X n × Cochain C X n) where
  toFun a := ((Cochain.ofHom biprod.inl).comp a (zero_add n),
    (Cochain.ofHom biprod.inr).comp a (zero_add n))
  invFun a := (Cochain.ofHom biprod.fst).comp a.1 (zero_add n) +
    (Cochain.ofHom biprod.snd).comp a.2 (zero_add n)
  left_inv a := by
    dsimp only
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
      ← Cochain.ofHom_comp, ← Cochain.add_comp, ← Cochain.ofHom_add,
      biprod.total, Cochain.id_comp]
  right_inv a := by
    apply Prod.ext
    · simp only [Cochain.comp_add, ← Cochain.comp_assoc_of_first_is_zero_cochain,
        ← Cochain.ofHom_comp, biprod.inl_fst, biprod.inl_snd, Cochain.ofHom_zero,
        Cochain.zero_comp, add_zero, Cochain.id_comp]
    · simp only [Cochain.comp_add, ← Cochain.comp_assoc_of_first_is_zero_cochain,
        ← Cochain.ofHom_comp, biprod.inr_fst, biprod.inr_snd, Cochain.ofHom_zero,
        Cochain.zero_comp, zero_add, Cochain.id_comp]
  map_add' a b := by
    apply Prod.ext <;> exact Cochain.comp_add _ _ _ (zero_add n)
  map_smul' c a := by
    apply Prod.ext <;> exact Cochain.comp_smul _ _ _ (zero_add n)

/-- 概要：逆座標は二つの射影による前合成の和。
方針：線形同値の逆を評価する。
規約：同じ次数の二成分を使う。使われ方：脚側右辺の合成。 -/
lemma biproductFromHomCoordinates_symm (n : ℤ) (a : Cochain B X n × Cochain C X n) :
    (biproductFromHomCoordinates B C X n).symm a =
      (Cochain.ofHom biprod.fst).comp a.1 (zero_add n) +
        (Cochain.ofHom biprod.snd).comp a.2 (zero_add n) := rfl

/-- 概要：直和から出る Hom の逆座標は微分と可換。
方針：微分の加法性と閉零の射影の前合成に対する Leibniz 則を使う。
規約：全次数。使われ方：cone の逆座標の微分の二脚成分。 -/
lemma biproductFromHomCoordinates_symm_differential (n : ℤ)
    (a : Cochain B X n) (b : Cochain C X n) :
    δ n (n + 1) ((biproductFromHomCoordinates B C X n).symm (a, b)) =
      (biproductFromHomCoordinates B C X (n + 1)).symm
        (δ n (n + 1) a, δ n (n + 1) b) := by
  simp only [biproductFromHomCoordinates_symm, δ_add, δ_zero_cochain_comp,
    δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
