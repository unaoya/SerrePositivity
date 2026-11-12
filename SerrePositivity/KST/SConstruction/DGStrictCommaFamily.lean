module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaCategory

/-! # 全 Hom 上の閉比較から作る実 dg comma の対象と作用
概要：元の二 dg 関手と全次数で自然な閉比較から、同じ comma 対象と全 Hom 作用を作る。
方針：同じ二つの鎖写像の比較差が零であることを使い、比較 cochain 零で持ち上げる。
規約：通常の閉零射だけの自然性へ弱めない。使われ方：標準 dg gluing 対角の構成。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (P : Type t) [DGCategory R P]

/-- 元の二関手と、全 Hom 鎖写像上で自然な同じ閉比較の族。 -/
structure DGStrictCommaFamily where
  source : DGFunctor R P C
  replacement : DGFunctor R P E
  augmentation : ∀ x, ForgetEnrichment.of (Complex R) (replacement.obj x) ⟶
    ForgetEnrichment.of (Complex R) (F.obj (source.obj x))
  naturality : ∀ x y,
    source.map x y ≫ F.map (source.obj x) (source.obj y) ≫
      eHomWhiskerRight (Complex R) (augmentation x)
        (ForgetEnrichment.of (Complex R) (F.obj (source.obj y))) =
    replacement.map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (replacement.obj x)) (augmentation y)

namespace DGStrictCommaFamily
variable {R C E F P} (d : DGStrictCommaFamily R C E F P)

/-- 元の二成分と同じ閉比較を持つ実 comma 対象。 -/
def obj (x : P) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F :=
  ⟨d.source.obj x, d.replacement.obj x, d.augmentation x⟩

/-- 元の全 Hom 上の自然性は、同じ比較差の鎖写像の零性を与える。 -/
lemma difference_zero (x y : P) :
    biprod.lift (d.source.map x y) (d.replacement.map x y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F (d.obj x) (d.obj y) = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_lift_difference (d.source.map x y) (d.replacement.map x y)
    (F.map (d.source.obj x) (d.source.obj y) ≫
      eHomWhiskerRight (Complex R) (d.augmentation x)
        (ForgetEnrichment.of (Complex R) (F.obj (d.source.obj y))))
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (d.replacement.obj x)) (d.augmentation y))).trans
        (sub_eq_zero.mpr (d.naturality x y))

/-- 同じ比較 cochain 零は、元の二つの鎖写像の持ち上げ境界条件を満たす。 -/
lemma boundary (x y : P) :
    δ (-1) 0 (0 : Cochain (homObject R P x y)
      (homObject R E (d.obj x).replacement (F.obj (d.obj y).source)) (-1)) +
      Cochain.ofHom (biprod.lift (d.source.map x y) (d.replacement.map x y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F (d.obj x) (d.obj y)) = 0 := by
  rw [d.difference_zero]
  simp

/-- 元の両関手の全 Hom 作用と同じ零比較を持つ実鎖写像。 -/
def homMap (x y : P) : homObject R P x y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F (d.obj x) (d.obj y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F (d.obj x) (d.obj y) _
    (d.source.map x y) (d.replacement.map x y) 0 (d.boundary x y)

/-- 同じ全 Hom 作用の実入力射影は、元の入力関手の作用。 -/
lemma homMap_source (x y : P) : d.homMap x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F (d.obj x) (d.obj y) = d.source.map x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R C E F (d.obj x) (d.obj y) _ _ _ _ _

/-- 同じ全 Hom 作用の実比較対象射影は、元の比較対象関手の作用。 -/
lemma homMap_replacement (x y : P) : d.homMap x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F (d.obj x) (d.obj y) = d.replacement.map x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R C E F (d.obj x) (d.obj y) _ _ _ _ _

/-- 同じ全 Hom 作用の比較 cochain は、指定した零そのもの。 -/
lemma homMap_comparison (x y : P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F (d.obj x) (d.obj y) _ (d.homMap x y) = 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, homMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex]
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F (d.obj x) (d.obj y))
    (biprod.lift (d.source.map x y) (d.replacement.map x y)) 0 (d.boundary x y) p q hpq

end DGStrictCommaFamily
end SerrePositivity.KST.SConstruction
