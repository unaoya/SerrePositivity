module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFirstStage
public import SerrePositivity.KST.SConstruction.StableKanAssemblySpanNaturality
public import SerrePositivity.KST.SConstruction.PointedTensorComparison
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerNaturality

/-!
概要：有限 native BF の実際の前段への比較から、同じ次段 span の両脚を作る。
方針：元の実 span を同じ有限入力に制限し、左脚へ前段比較の suspension を合成する。
規約：実際の前段の suspension を使う。使われ方：新四辺と全二胞体の同時再帰。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (r : ℕ)

/-- 概要：元の同じ隣接段 span の有限入力上の源。
方針：元の全族 span を同じ豊穣包含へ制限する。
規約：同じ二胞体を保つ。使われ方：有限 BF 次段の実始域。 -/
def dgKappaNativeBFFiniteAssemblySourceFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteInclusion.{u, v} R D I).comp SSet (stableKanAssemblySourceFunctor r)

/-- 概要：同じ有限入力の元の正段の suspension。
方針：元の境界商関手を同じ円で suspension する。
規約：実際の前段とは区別する。使われ方：次段左脚の中間値。 -/
def dgKappaNativeBFFiniteAssemblyLeftTargetFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).comp SSet
    (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})

/-- 概要：同じ全族左標的の Hom 作用は元の実 span の作用。
方針：有限包含の恒等作用と同じ三関手の合成の括弧を照合する。
規約：元の全単体の等式。使われ方：実左脚の全 Hom 自然性。 -/
lemma dgKappaNativeBFFiniteAssemblyLeftTarget_map
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblyLeftTargetFunctor.{u, v} R D I r).map C E =
      (stableKanAssemblyLeftTargetFunctor r).map C.obj E.obj := by
  change (𝟙 _ ≫ ((stableBoundaryPointedEnrichedFunctor r).map C.obj E.obj ≫
      exInfinityPointedEnrichedFunctor.map _ _)) ≫
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map _ _ =
    (stableBoundaryPointedEnrichedFunctor r).map C.obj E.obj ≫
      (exInfinityPointedEnrichedFunctor.map _ _ ≫
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map _ _)
  rw [Category.id_comp, Category.assoc]

/-- 概要：同じ有限入力の元の左比較脚。
方針：元の実 span の左脚を同じ頂点へ制限する。
規約：比較を選び直さない。使われ方：実際の前段への左脚の延長。 -/
def dgKappaNativeBFFiniteAssemblyLeftMap (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C ⟶
      (dgKappaNativeBFFiniteAssemblyLeftTargetFunctor.{u, v} R D I r).obj C :=
  stableKanAssemblyLeftMap r C.obj

/-- 概要：同じ有限入力の元の右組み立て脚。
方針：元の実 span の右脚を同じ頂点へ制限する。
規約：元の隣接正段へ写す。使われ方：有限 BF 次段の右脚。 -/
def dgKappaNativeBFFiniteAssemblyRightMap (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C ⟶
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C :=
  stableKanAssemblyRightMap r C.obj

/-- 概要：同じ有限左脚は全 Hom に厳密に自然。
方針：同じ充満包含と元の左自然性を使う。
規約：元の全高次入力を保つ。使われ方：次段の左脚の自然性。 -/
lemma dgKappaNativeBFFiniteAssemblyLeft_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).map C E ≫
        eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C)
          (dgKappaNativeBFFiniteAssemblyLeftMap.{u, v} R D I r E) =
      (dgKappaNativeBFFiniteAssemblyLeftTargetFunctor.{u, v} R D I r).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteAssemblyLeftMap.{u, v} R D I r C)
          ((dgKappaNativeBFFiniteAssemblyLeftTargetFunctor.{u, v} R D I r).obj E) := by
  change (𝟙 _ ≫ (stableKanAssemblySourceFunctor r).map C.obj E.obj) ≫ _ = _
  rw [Category.id_comp, dgKappaNativeBFFiniteAssemblyLeftTarget_map]
  exact stableKanAssemblyLeft_whisker r C.obj E.obj

/-- 概要：同じ有限右脚は全 Hom に厳密に自然。
方針：充満包含の恒等作用後に元の右自然性を使う。
規約：元の全二胞体を保つ。使われ方：有限 BF 次段の右可換式。 -/
lemma dgKappaNativeBFFiniteAssemblyRight_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).map C E ≫
        eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C)
          (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r E) =
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r C)
          ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj E) := by
  change (𝟙 _ ≫ (stableKanAssemblySourceFunctor r).map C.obj E.obj) ≫
      eHomWhiskerLeft SSet ((stableKanAssemblySourceFunctor r).obj C.obj)
        (stableKanAssemblyRightMap r E.obj) =
    (𝟙 _ ≫ (stableKanAssemblyTargetFunctor r).map C.obj E.obj) ≫
      eHomWhiskerRight SSet (stableKanAssemblyRightMap r C.obj)
        ((stableKanAssemblyTargetFunctor r).obj E.obj)
  rw [Category.id_comp, Category.id_comp]
  exact stableKanAssemblyRight_whisker r C.obj E.obj

variable (K : EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
    PointedSSetObject.{max (u + 1) v})
  (c : ∀ C, (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C ⟶ K.obj C)
  (hc : ∀ C E, (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).map C E ≫
      eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C) (c E) =
    K.map C E ≫ eHomWhiskerRight SSet (c C) (K.obj E))

/-- 概要：元の左脚から実際の前段の suspension への実合成脚。
方針：同じ元の左脚へ前向き比較の suspension を合成する。
規約：元の正段で前段を代用しない。使われ方：有限 BF 実次段の構成。 -/
def dgKappaNativeBFFiniteStepLeftMap (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C ⟶
      (K.comp SSet (pointedTensorEnrichedFunctor
        PointedSimplicialSet.circle.{max (u + 1) v})).obj C :=
  dgKappaNativeBFFiniteAssemblyLeftMap.{u, v} R D I r C ≫
    PointedSimplicialSet.circle.{max (u + 1) v} ◁
      (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
        (K.obj C).obj from c C)

include hc in
/-- 概要：実際の前段への同じ合成左脚は全 Hom に自然。
方針：元の左自然性と同じ前向き比較の suspension の自然性を合成する。
規約：同じ全入力を保持。使われ方：有限 BF 次段の全二胞体の保存。 -/
lemma dgKappaNativeBFFiniteStepLeft_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).map C E ≫
        eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C)
          (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r K c E) =
      (K.comp SSet (pointedTensorEnrichedFunctor
        PointedSimplicialSet.circle.{max (u + 1) v})).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r K c C)
          ((K.comp SSet (pointedTensorEnrichedFunctor
        PointedSimplicialSet.circle.{max (u + 1) v})).obj E) :=
  enriched_whisker_naturality_comp SSet _ _ _ _ _ _ _
    (dgKappaNativeBFFiniteAssemblyLeft_whisker.{u, v} R D I r C E)
    (pointedTensorComparison_whisker PointedSimplicialSet.circle.{max (u + 1) v}
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r) K c hc C E)

end SerrePositivity.KST.SConstruction
