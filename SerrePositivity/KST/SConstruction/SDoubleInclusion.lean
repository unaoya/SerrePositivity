module
public import SerrePositivity.KST.SConstruction.SInterchangeIso
public import SerrePositivity.KST.SConstruction.StableModels

/-! # 二重 S 構成の二重内部 Hom への忠実な表示
概要：二つの gapped 包含を合成した単射を用い、二重 S の後合成と両添字の制限を記述する。
方針：既存の包含の式と内部 Hom の自然性を合成する。
規約：全高次パラメーターを保つ。使われ方：交換の入力・面・退化についての自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 二重 S 構成の二つの gapped 包含による二重内部 Hom への射。 -/
def sDoubleInclusion (m n : ℕ) (C : SSet.{u}) :
    sConstruction m (sConstruction n C) ⟶ (ihom (arNerve m)).obj ((ihom (arNerve n)).obj C) :=
  (gappedSubcomplex m (sConstruction n C)).ι ≫
    (ihom (arNerve m)).map (gappedSubcomplex n C).ι

/-- 二重 S 構成の二重包含は単射。 -/
instance sDoubleInclusion_mono (m n : ℕ) (C : SSet.{u}) : Mono (sDoubleInclusion m n C) := by
  have : Mono ((ihom (arNerve m)).map (gappedSubcomplex n C).ι) :=
    (ihom (arNerve m)).map_mono _
  exact inferInstanceAs (Mono ((gappedSubcomplex m (sConstruction n C)).ι ≫
    (ihom (arNerve m)).map (gappedSubcomplex n C).ι))

/-- 二重包含の表示上で S の交換は元の内部 Hom の交換。 -/
lemma sInterchange_doubleInclusion (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sInterchange m n C ≫ sDoubleInclusion n m C = sDoubleInclusion m n C ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (arNerve n) C).hom :=
  (Category.assoc _ _ _).symm.trans (sInterchange_double_ι m n C)

/-- 二重 S の完全な後合成は二重内部 Hom の後合成を厳密に回収する。 -/
lemma sDoubleInclusion_postcomp (m n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ((sEndofunctor m).map ((sEndofunctor n).map f)).val ≫ sDoubleInclusion m n Y.carrier =
      sDoubleInclusion m n X.carrier ≫ (ihom (arNerve m)).map ((ihom (arNerve n)).map f.val) := by
  let q := (sEndofunctor n).map f
  have hm : ((sEndofunctor m).map q).val ≫
      (gappedSubcomplex m (sConstruction n Y.carrier)).ι =
    (gappedSubcomplex m (sConstruction n X.carrier)).ι ≫ (ihom (arNerve m)).map q.val :=
    sPostcompCofiber_ι m q.val q.property
  have hn : q.val ≫ (gappedSubcomplex n Y.carrier).ι =
      (gappedSubcomplex n X.carrier).ι ≫ (ihom (arNerve n)).map f.val :=
    sPostcompCofiber_ι n f.val f.property
  change ((sEndofunctor m).map q).val ≫
    ((gappedSubcomplex m (sConstruction n Y.carrier)).ι ≫
      (ihom (arNerve m)).map (gappedSubcomplex n Y.carrier).ι) = _
  rw [← Category.assoc, hm, Category.assoc, ← CategoryTheory.Functor.map_comp,
    hn, CategoryTheory.Functor.map_comp, ← Category.assoc]
  rfl

/-- 外側の添字の制限は二重内部 Hom の最初の変数の制限を厳密に回収する。 -/
lemma sDoubleInclusion_outerMap {m m' : ℕ} (n : ℕ) (C : SSet.{u})
    (θ : Fin (m' + 1) →o Fin (m + 1)) :
    sMap (sConstruction n C) θ ≫ sDoubleInclusion m' n C =
      sDoubleInclusion m n C ≫ (pre (arNerveMap θ)).app ((ihom (arNerve n)).obj C) := by
  have hn : (pre (arNerveMap θ)).app (sConstruction n C) ≫
      (ihom (arNerve m')).map (gappedSubcomplex n C).ι =
    (ihom (arNerve m)).map (gappedSubcomplex n C).ι ≫
      (pre (arNerveMap θ)).app ((ihom (arNerve n)).obj C) :=
    ((pre (arNerveMap θ)).naturality (gappedSubcomplex n C).ι).symm
  change sMap (sConstruction n C) θ ≫
    ((gappedSubcomplex m' (sConstruction n C)).ι ≫
      (ihom (arNerve m')).map (gappedSubcomplex n C).ι) = _
  rw [← Category.assoc, sMap_ι, Category.assoc,
    hn, ← Category.assoc]
  rfl

/-- 内側の添字の制限は二重内部 Hom の第二の変数の制限を厳密に回収する。 -/
lemma sDoubleInclusion_innerMap (m : ℕ) {n n' : ℕ} (X : StableModel.{u})
    (θ : Fin (n' + 1) →o Fin (n + 1)) :
    ((sEndofunctor m).map ((sEndofunctorMap θ).app X)).val ≫
        sDoubleInclusion m n' X.carrier = sDoubleInclusion m n X.carrier ≫
      (ihom (arNerve m)).map ((pre (arNerveMap θ)).app X.carrier) := by
  let q := (sEndofunctorMap θ).app X
  have hm : ((sEndofunctor m).map q).val ≫
      (gappedSubcomplex m (sConstruction n' X.carrier)).ι =
    (gappedSubcomplex m (sConstruction n X.carrier)).ι ≫ (ihom (arNerve m)).map q.val :=
    sPostcompCofiber_ι m q.val q.property
  have hn : q.val ≫ (gappedSubcomplex n' X.carrier).ι =
      (gappedSubcomplex n X.carrier).ι ≫ (pre (arNerveMap θ)).app X.carrier :=
    sMap_ι X.carrier θ
  change ((sEndofunctor m).map q).val ≫
    ((gappedSubcomplex m (sConstruction n' X.carrier)).ι ≫
      (ihom (arNerve m)).map (gappedSubcomplex n' X.carrier).ι) = _
  rw [← Category.assoc, hm, Category.assoc, ← CategoryTheory.Functor.map_comp,
    hn, CategoryTheory.Functor.map_comp, ← Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
