module
public import SerrePositivity.KST.SConstruction.DGStrictCommaFunctor
public import SerrePositivity.KST.SConstruction.DGGluingFunctorLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Projections

/-! # 二つの元の dg 関手と閉元から作る実 gluing 関手
概要：左右の実関手と双加群の閉元を使い、全 Hom を持つ実 gluing 関手を作る。
方針：Yoneda 表示の自然性から comma 関手を構成し、元の Hom 同型で戻す。
規約：対角関手自体を入力に仮定しない。使われ方：Perf の標準対角の具体化。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma dgFunctorCompAssoc {R : Type u} [CommRing R]
    {B : Type*} {C : Type*} {D : Type*} {E : Type*}
    [DGCategory R B] [DGCategory R C] [DGCategory R D] [DGCategory R E]
    (H : DGFunctor R B C) (J : DGFunctor R C D) (K : DGFunctor R D E) :
    (H.comp J).comp K = H.comp (J.comp K) := by
  apply EnrichedFunctor.ext (Complex R) (F := (H.comp J).comp K)
    (G := H.comp (J.comp K)) (fun _ => rfl)
  intro x y
  change ((H.map x y ≫ J.map (H.obj x) (H.obj y)) ≫
    K.map (J.obj (H.obj x)) (J.obj (H.obj y))) ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.assoc]
  rfl

private lemma dgFunctorMapOfEq {R : Type u} [CommRing R]
    {B : Type*} {C : Type*} [DGCategory R B] [DGCategory R C]
    (H J : DGFunctor R B C) (he : H = J) (ho : ∀ x, H.obj x = J.obj x) (x y : B) :
    H.map x y ≫ eqToHom (congrArg₂ (homObject R C) (ho x) (ho y)) = J.map x y := by
  cases he
  simp only [eqToHom_refl, Category.comp_id]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {P : Type t} [DGCategory R P]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (μ : ∀ x, zeroCycles (M.value (L.obj x) (G.obj x)))

/-- 元の左右対象と同じ双加群の閉元を持つ実 gluing 対象。 -/
def dgStrictGluingObject (x : P) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M :=
  ⟨L.obj x, G.obj x, μ x⟩

variable (h : ∀ x y,
  G.map x y ≫ M.toFunctor.map (G.obj x) (G.obj y) ≫
    eHomWhiskerRight (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgStrictGluingObject R C D M L G μ x))
      (ForgetEnrichment.of (Complex R) (M.toFunctor.obj (G.obj y))) =
  (L.comp (dgYoneda R C)).map x y ≫
    eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R (L.obj x)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgStrictGluingObject R C D M L G μ y)))

/-- 元の二成分と閉元の全 Hom 自然性から構成する実 comma 比較族。 -/
def dgStrictGluingCommaFamily : DGStrictCommaFamily R D (RightModule R C) M.toFunctor P where
  source := G
  replacement := L.comp (dgYoneda R C)
  augmentation x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgStrictGluingObject R C D M L G μ x)
  naturality := h

/-- 元の左右関手と閉元から作る、全 Hom の単位・合成を保つ実 gluing 関手。 -/
def dgStrictGluingFunctor : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  dgGluingFunctorLiftOfEq R C D M
    (dgStrictGluingCommaFamily R C D M L G μ h).toDGFunctor
    (dgStrictGluingObject R C D M L G μ) (fun _ => rfl)

/-- 同じ関手の対象は、元の左右対象と同じ閉元をそのまま保持する。 -/
lemma dgStrictGluingFunctor_obj (x : P) :
    (dgStrictGluingFunctor R C D M L G μ h).obj x =
      dgStrictGluingObject R C D M L G μ x := rfl

/-- 元の comma 表示への像は、二関手と閉比較から作った同じ実関手。 -/
lemma dgStrictGluingFunctor_toComma :
    (dgStrictGluingFunctor R C D M L G μ h).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) =
      (dgStrictGluingCommaFamily R C D M L G μ h).toDGFunctor :=
  dgGluingFunctorLiftOfEq_toComma R C D M
    (dgStrictGluingCommaFamily R C D M L G μ h).toDGFunctor
    (dgStrictGluingObject R C D M L G μ) (fun _ => rfl)

/-- 同じ実 gluing 関手の右射影は、元の右関手そのもの。 -/
lemma dgStrictGluingFunctor_right :
    (dgStrictGluingFunctor R C D M L G μ h).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) = G :=
  (dgFunctorCompAssoc (dgStrictGluingFunctor R C D M L G μ h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor)).symm.trans
      ((congrArg (fun k => k.comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor))
        (dgStrictGluingFunctor_toComma R C D M L G μ h)).trans
          (dgStrictGluingCommaFamily R C D M L G μ h).toDGFunctor_source)

/-- 同じ実 gluing 関手の左加群射影は、元の左関手の同じ Yoneda 表示。 -/
lemma dgStrictGluingFunctor_leftModule :
    (dgStrictGluingFunctor R C D M L G μ h).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule R C D M) =
      L.comp (dgYoneda R C) :=
  (dgFunctorCompAssoc (dgStrictGluingFunctor R C D M L G μ h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor)).symm.trans
      ((congrArg (fun k => k.comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor))
        (dgStrictGluingFunctor_toComma R C D M L G μ h)).trans
          (dgStrictGluingCommaFamily R C D M L G μ h).toDGFunctor_replacement)

/-- 同じ実 gluing 関手の左射影は、元の左関手そのもの。 -/
lemma dgStrictGluingFunctor_left :
    (dgStrictGluingFunctor R C D M L G μ h).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) = L := by
  let S := dgStrictGluingFunctor R C D M L G μ h
  apply EnrichedFunctor.ext (Complex R) (F := S.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M))
    (G := L) (fun _ => rfl)
  intro x y
  change (S.map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M (S.obj x) (S.obj y)) ≫ 𝟙 _ = L.map x y
  rw [Category.comp_id]
  have : IsIso (yonedaHom R C (L.obj x) (L.obj y)) := by
    change IsIso (dgYonedaIso R (L.obj x) (representable R (L.obj y))).inv
    infer_instance
  apply (cancel_mono (yonedaHom R C (L.obj x) (L.obj y))).mp
  have hm := dgFunctorMapOfEq (S.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule R C D M))
    (L.comp (dgYoneda R C)) (dgStrictGluingFunctor_leftModule R C D M L G μ h)
    (fun _ => rfl) x y
  change (S.map x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule R C D M).map (S.obj x) (S.obj y)) ≫ 𝟙 _ =
    L.map x y ≫ yonedaHom R C (L.obj x) (L.obj y) at hm
  rw [Category.comp_id] at hm
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule_map] at hm
  exact (Category.assoc _ _ _).trans hm

end SerrePositivity.KST.SConstruction
