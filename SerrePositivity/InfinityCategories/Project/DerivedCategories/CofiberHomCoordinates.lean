module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Mapping cone からの Hom の全次数座標

概要：mapping cone から出る cochain を二つの包含の成分で表示し、微分を計算する。
方針：Mathlib の inl・inr と descCochain を互いに逆として使う。
規約：cone からの次数 n+1 の射の第一座標は次数 n。
使われ方：D7 の cofiber の coslice の境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {S : Type u} [CommRing S] {B D X : Complex S}

/-- 概要：cone からの cochain は二つの包含後の成分と線形に同値。
方針：順方向は inl・inr の前合成、逆方向は descCochain。
規約：次数 n+1 の cochain に対して座標の次数は n と n+1。
使われ方：cofiber から出る全次数の射の明示解。 -/
def cofiberHomCoordinates (f : B ⟶ D) (n : ℤ) :
    Cochain (mappingCone f) X (n + 1) ≃ₗ[S]
      (Cochain B X n × Cochain D X (n + 1)) where
  toFun a := ((mappingCone.inl f).comp a (by omega),
    (Cochain.ofHom (mappingCone.inr f)).comp a (zero_add (n + 1)))
  invFun a := mappingCone.descCochain f a.1 a.2 rfl
  left_inv a := by
    apply (mappingCone.ext_cochain_from_iff f n (n + 1) rfl).2
    exact ⟨mappingCone.inl_descCochain _ _ _ _, mappingCone.inr_descCochain _ _ _ _⟩
  right_inv a := by
    apply Prod.ext
    · exact mappingCone.inl_descCochain _ _ _ _
    · exact mappingCone.inr_descCochain _ _ _ _
  map_add' a b := by
    apply Prod.ext
    · exact Cochain.comp_add _ _ _ (by omega)
    · exact Cochain.comp_add _ _ _ (zero_add (n + 1))
  map_smul' c a := by
    apply Prod.ext
    · exact Cochain.comp_smul _ _ _ (by omega)
    · exact Cochain.comp_smul _ _ _ (zero_add (n + 1))

/-- 概要：第一座標は次数 -1 の包含の前合成。
方針：線形同値の第一成分を評価する。
規約：次数 n の座標。使われ方：cone 側のホモトピー成分。 -/
lemma cofiberHomCoordinates_fst (f : B ⟶ D) (n : ℤ)
    (a : Cochain (mappingCone f) X (n + 1)) :
    (cofiberHomCoordinates f n a).1 = (mappingCone.inl f).comp a (by omega) := rfl

/-- 概要：第二座標は標準の鎖写像の包含の前合成。
方針：線形同値の第二成分を評価する。
規約：次数 n+1 の座標。使われ方：cofiber の標準包含との合成。 -/
lemma cofiberHomCoordinates_snd (f : B ⟶ D) (n : ℤ)
    (a : Cochain (mappingCone f) X (n + 1)) :
    (cofiberHomCoordinates f n a).2 =
      (Cochain.ofHom (mappingCone.inr f)).comp a (zero_add (n + 1)) := rfl

/-- 概要：逆座標写像は Mathlib の descCochain。
方針：線形同値の逆写像を評価する。
規約：次数の一致は反射律。使われ方：coslice の未知成分の構成。 -/
lemma cofiberHomCoordinates_symm (f : B ⟶ D) (n : ℤ)
    (a : Cochain B X n × Cochain D X (n + 1)) :
    (cofiberHomCoordinates f n).symm a = mappingCone.descCochain f a.1 a.2 rfl := rfl

/-- 概要：逆座標写像の微分は第一成分に cone の接続項を加える。
方針：Mathlib の descCochain の微分式を座標表示へ戻す。
規約：接続項の符号は (n+2).negOnePow。使われ方：cofiber の全次数の残差方程式。 -/
lemma cofiberHomCoordinates_symm_differential (f : B ⟶ D) (n : ℤ)
    (a : Cochain B X n) (b : Cochain D X (n + 1)) :
    δ (n + 1) (n + 1 + 1) ((cofiberHomCoordinates f n).symm (a, b)) =
      (cofiberHomCoordinates f (n + 1)).symm
        (δ n (n + 1) a + (n + 1 + 1).negOnePow •
          (Cochain.ofHom f).comp b (zero_add (n + 1)),
          δ (n + 1) (n + 1 + 1) b) :=
  mappingCone.δ_descCochain f a b rfl _ rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
