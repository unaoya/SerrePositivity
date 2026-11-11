module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardCofiberSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BiproductFromHomCoordinates

/-! # 標準 cofiber から出る Hom の三成分表示

概要：標準 cofiber から出る Hom は A からの一段低い成分と B・C からの成分に線形に同値。
方針：cone と二項直和の二つの座標を合成し、微分を明示する。
規約：全整数次数。使われ方：D7 の coslice 境界の明示的な充填成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C X : Complex S}

/-- 概要：標準 cofiber から出る Hom の全次数の三成分の線形同値。
方針：cone の第二座標を直和の二成分に分ける。
規約：第一成分は一段低い次数。使われ方：六成分の明示解の構成。 -/
def pushoutHomCoordinates (f : A ⟶ B) (g : A ⟶ C) (n : ℤ) :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (n + 1) ≃ₗ[S]
      (Cochain A X n × (Cochain B X (n + 1) × Cochain C X (n + 1))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g) n).trans
    ((LinearEquiv.refl S _).prodCongr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.biproductFromHomCoordinates B C X (n + 1)))

/-- 概要：三成分からの復元は、二脚を直和から出る成分にまとめて cone から復元する。
方針：線形同値の合成の逆を評価する。
規約：全次数。使われ方：未知成分の座標の計算。 -/
lemma pushoutHomCoordinates_symm (f : A ⟶ B) (g : A ⟶ C) (n : ℤ)
    (a : Cochain A X n × (Cochain B X (n + 1) × Cochain C X (n + 1))) :
    (pushoutHomCoordinates f g n).symm a =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g) n).symm
        (a.1, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.biproductFromHomCoordinates B C X (n + 1)).symm a.2) := rfl

/-- 概要：差の射の前合成は二つの脚の合成の差。
方針：射影との合成を評価して直和の逆座標の二項を簡約する。
規約：差の第二成分は -g。使われ方：cone の接続項の展開。 -/
lemma cofiberDifference_comp_biproductFromHomCoordinates
    (f : A ⟶ B) (g : A ⟶ C) (n : ℤ) (a : Cochain B X n) (b : Cochain C X n) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)).comp
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.biproductFromHomCoordinates B C X n).symm (a, b)) (zero_add n) =
      (Cochain.ofHom f).comp a (zero_add n) - (Cochain.ofHom g).comp b (zero_add n) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.biproductFromHomCoordinates_symm, Cochain.comp_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference, biprod.lift_fst, biprod.lift_snd, Cochain.ofHom_neg,
    Cochain.neg_comp, sub_eq_add_neg]

/-- 概要：三成分の逆座標の微分は cone の接続項を加える行列微分。
方針：cone と直和の微分公式を合成し、差の射を二つの脚へ展開する。
規約：接続項の符号は (n+2).negOnePow。使われ方：未知成分の微分方程式。 -/
lemma pushoutHomCoordinates_symm_differential (f : A ⟶ B) (g : A ⟶ C) (n : ℤ)
    (a : Cochain A X n) (b : Cochain B X (n + 1)) (c : Cochain C X (n + 1)) :
    δ (n + 1) (n + 1 + 1) ((pushoutHomCoordinates f g n).symm (a, (b, c))) =
      (pushoutHomCoordinates f g (n + 1)).symm
        (δ n (n + 1) a + (n + 1 + 1).negOnePow •
          ((Cochain.ofHom f).comp b (zero_add (n + 1)) -
            (Cochain.ofHom g).comp c (zero_add (n + 1))),
          (δ (n + 1) (n + 1 + 1) b, δ (n + 1) (n + 1 + 1) c)) := by
  rw [pushoutHomCoordinates_symm, pushoutHomCoordinates_symm,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberHomCoordinates_symm_differential, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.biproductFromHomCoordinates_symm_differential,
    cofiberDifference_comp_biproductFromHomCoordinates]

/-- 概要：第一座標は cone の次数 −1 の包含との前合成。
方針：合成した線形同値の第一座標を評価する。
規約：一段低い次数。使われ方：三角形側の残差。 -/
lemma pushoutHomCoordinates_apex_eq_comp (f : A ⟶ B) (g : A ⟶ C) (n : ℤ)
    (a : Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (n + 1)) :
    (pushoutHomCoordinates f g n a).1 =
      (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)).comp a (by omega) := rfl

/-- 概要：B 座標は標準の B からの包含との前合成。
方針：cone と直和の座標の定義と合成の結合律を使う。
規約：次数 n+1。使われ方：脚側の未知成分の比較。 -/
lemma pushoutHomCoordinates_left_eq_comp (f : A ⟶ B) (g : A ⟶ C) (n : ℤ)
    (a : Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (n + 1)) :
    (pushoutHomCoordinates f g n a).2.1 =
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)).comp a (zero_add (n + 1)) := by
  change (Cochain.ofHom biprod.inl).comp
    ((Cochain.ofHom (mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g))).comp a (zero_add (n + 1)))
      (zero_add (n + 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB, Cochain.ofHom_comp]
  exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add (n + 1))).symm

/-- 概要：C 座標は標準の C からの包含との前合成。
方針：cone と直和の座標の定義と合成の結合律を使う。
規約：次数 n+1。使われ方：脚側の未知成分の比較。 -/
lemma pushoutHomCoordinates_right_eq_comp (f : A ⟶ B) (g : A ⟶ C) (n : ℤ)
    (a : Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (n + 1)) :
    (pushoutHomCoordinates f g n a).2.2 =
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).comp a (zero_add (n + 1)) := by
  change (Cochain.ofHom biprod.inr).comp
    ((Cochain.ofHom (mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g))).comp a (zero_add (n + 1)))
      (zero_add (n + 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC, Cochain.ofHom_comp]
  exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add (n + 1))).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
