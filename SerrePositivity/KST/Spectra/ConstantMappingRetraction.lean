module

public import SerrePositivity.KST.Spectra.ConstantPointedHomotopyCone
public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
概要：非空の源からの写像空間への定数射は評価射で分裂する。
方針：源の選んだ点への制限を単位の内部 Hom の評価と合成する。
規約：源の点は単位単体集合からの射で指定する。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射の単射性の確認。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単位単体集合からの写像空間は元の点つき係数と同型。
方針：通常の内部 Hom の単位同型が定数基点を保つことを確認する。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7、VIII §2。定数写像の評価による分裂。 -/
def unitIso (X : PointedSimplicialSet.{u}) : obj (𝟙_ SSet.{u}) X ≅ X :=
  Under.isoMk (unitIsoSelf (X := X.right)) (by
    change curry (snd (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) ≫ X.hom) ≫
      (unitIsoSelf (X := X.right)).hom = X.hom
    rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curry_unit_evaluation]
    change (λ_ (𝟙_ SSet.{u})).inv ≫ (λ_ (𝟙_ SSet.{u})).hom ≫ X.hom = X.hom
    simp)

/-- 概要：選んだ源の点で写像を評価する点つき射。
方針：点への前合成の後で単位の内部 Hom を評価する。
規約：点は K の頂点と同じ情報を持つ単位からの射。
使われ方：Goerss–Jardine VIII §2。標準比較の左逆。 -/
def evaluation {K : SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ K) (X : PointedSimplicialSet.{u}) :
    obj K X ⟶ X := pre v X ≫ (unitIso X).hom

lemma constant_pre {K L : SSet.{u}} (f : K ⟶ L) (X : PointedSimplicialSet.{u}) :
    constant L X ≫ pre f X = constant K X := by
  apply Under.UnderMorphism.ext
  change curry (snd L X.right) ≫ (MonoidalClosed.pre f).app X.right =
    curry (snd K X.right)
  rw [curry_pre_app, whiskerRight_snd]

/-- 概要：定数写像を任意の点で評価すると元の係数に戻る。
方針：定数射の前合成の不変性と単位の内部 Hom の評価を使う。
規約：厳密な点つき射の等式。
使われ方：Goerss–Jardine VIII §2。有理性に依存しない標準射の分裂。 -/
@[reassoc (attr := simp)]
lemma constant_evaluation {K : SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ K)
    (X : PointedSimplicialSet.{u}) : constant K X ≫ evaluation v X = 𝟙 X := by
  rw [evaluation, ← Category.assoc, constant_pre]
  apply Under.UnderMorphism.ext
  change curry (snd (𝟙_ SSet.{u}) X.right) ≫ (unitIsoSelf (X := X.right)).hom = 𝟙 X.right
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curry_unit_evaluation]
  exact Iso.inv_hom_id (λ_ X.right)

/-- 概要：非空の源への定数射は全正次数の群で単射。
方針：評価の左逆を誘導群準同型へ送る。
規約：係数は Kan、源の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射の群での単射性。 -/
theorem constant_groupMap_injective {K : SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ K)
    (X : PointedSimplicialSet.{u}) [KanComplex X.right] (r : ℕ) :
    Function.Injective (pointedGroupMap (X := X) (Y := obj K X) r (constant K X)) := by
  apply Function.LeftInverse.injective (g := pointedGroupMap r (evaluation v X))
  intro a
  rw [← pointedGroupMap_comp, constant_evaluation, pointedGroupMap_id]

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
