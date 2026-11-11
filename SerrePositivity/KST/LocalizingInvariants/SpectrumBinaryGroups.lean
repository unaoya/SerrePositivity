module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryMaps
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
概要：元の BF 二項積の整数 π 群の積分解と両軸による表示。
方針：段ごとの直積の単射判定と、両軸の厳密な射影則を使う。
規約：群は元の二項積対象で計算する。使われ方：実 Sp 積比較の π 同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.Binary

lemma map_comp_apply {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap g j (homotopyMap f j a) = homotopyMap (f ≫ g) j a :=
  (DFunLike.congr_fun (homotopyMap_comp f g j) a).symm

lemma map_zero (X Y : OmegaSpectrum.{u}) (j : ℤ) : homotopyMap (0 : X ⟶ Y) j = 1 := by
  ext a
  rw [homotopyMap_apply, zero_app]
  simp only [PointedObject.zero_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const, MonoidHom.one_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const (X := (X.level (canonicalLevel j)).space.right)
    (Y := (Y.level (canonicalLevel j)).space.right) _ _ a).trans (levelPoint_eq_one Y _ _)

def groupProjection (X Y : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (obj X Y) j →* homotopyGroup X j × homotopyGroup Y j :=
  (homotopyMap (fst X Y) j).prod (homotopyMap (snd X Y) j)

lemma positive_projection_injective (X Y : OmegaSpectrum.{u}) (k n : ℕ) (hn : 0 < n) :
    Function.Injective
      ((positiveLevelMap (obj X Y) X k n hn (PointedObject.prodFst _ _)).prod
        (positiveLevelMap (obj X Y) Y k n hn (PointedObject.prodSnd _ _))) := by
  cases n with
  | zero => omega
  | succ n => exact pointedGroupProd_injective (X.level k).space (Y.level k).space n

lemma groupProjection_injective (X Y : OmegaSpectrum.{u}) (j : ℤ) :
    Function.Injective (groupProjection X Y j) :=
  positive_projection_injective X Y (canonicalLevel j) (degree j (canonicalLevel j))
    (canonicalDegree_pos j)

lemma axes (X Y : OmegaSpectrum.{u}) (j : ℤ) (a : homotopyGroup (obj X Y) j) :
    homotopyMap (inl X Y) j (homotopyMap (fst X Y) j a) *
      homotopyMap (inr X Y) j (homotopyMap (snd X Y) j a) = a := by
  apply groupProjection_injective X Y j
  apply Prod.ext
  · change homotopyMap (fst X Y) j (_ * _) = homotopyMap (fst X Y) j a
    simp only [map_mul, map_comp_apply, Category.assoc, inl_fst, inr_fst,
      Category.comp_id, Limits.comp_zero, map_zero, MonoidHom.one_apply, mul_one]
  · change homotopyMap (snd X Y) j (_ * _) = homotopyMap (snd X Y) j a
    simp only [map_mul, map_comp_apply, Category.assoc, inl_snd, inr_snd,
      Category.comp_id, Limits.comp_zero, map_zero, MonoidHom.one_apply, one_mul]

lemma groupProjection_surjective (X Y : OmegaSpectrum.{u}) (j : ℤ) :
    Function.Surjective (groupProjection X Y j) := by
  rintro ⟨a, b⟩
  refine ⟨homotopyMap (inl X Y) j a * homotopyMap (inr X Y) j b, ?_⟩
  apply Prod.ext
  · change homotopyMap (fst X Y) j (_ * _) = a
    simp only [map_mul, map_comp_apply, inl_fst, inr_fst, homotopyMap_id,
      map_zero, MonoidHom.id_apply, MonoidHom.one_apply, mul_one]
  · change homotopyMap (snd X Y) j (_ * _) = b
    simp only [map_mul, map_comp_apply, inl_snd, inr_snd, homotopyMap_id,
      map_zero, MonoidHom.id_apply, MonoidHom.one_apply, one_mul]

def groupEquiv (X Y : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (obj X Y) j ≃* homotopyGroup X j × homotopyGroup Y j :=
  MulEquiv.ofBijective (groupProjection X Y j)
    ⟨groupProjection_injective X Y j, groupProjection_surjective X Y j⟩

lemma lift_map {X Y A : OmegaSpectrum.{u}} (f : A ⟶ X) (g : A ⟶ Y)
    (j : ℤ) (a : homotopyGroup A j) :
    homotopyMap (lift f g) j a =
      homotopyMap (inl X Y) j (homotopyMap f j a) *
        homotopyMap (inr X Y) j (homotopyMap g j a) := by
  have h := axes X Y j (homotopyMap (lift f g) j a)
  simpa only [map_comp_apply, lift_fst, lift_snd] using h.symm

end SerrePositivity.KST.LocalizingInvariants.Binary
