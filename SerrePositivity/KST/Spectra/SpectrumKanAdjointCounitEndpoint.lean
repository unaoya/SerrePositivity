module

public import SerrePositivity.KST.Spectra.SignedLoopCounitCoordinates
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureCounit

/-!
概要：元の構造区間の counit 像の終点を、円交換と符号反転を明示した座標へ同定する。
方針：同じ普遍懸垂評価に、符号付き二重随伴の uncurry を後合成する。
規約：始点と終点の厳密な一致は未主張。
使われ方：HA §1.4.2。全列ホモトピーに必要な係数区間の残差の特定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

/-- 内部 Hom の後合成の counit 像は、同じ射の通常の円への制限を反復 uncurry したもの。 -/
lemma kanLoopCounit_post {U V : PointedSimplicialSet.{u}}
    (T : PointedSimplicialSet.{u})
    (f : U ⟶ PointedObject.basedHom CirclePower.space.{u} V) :
    PointedObject.basedHomMap T f ≫ kanLoopCounit T V =
      PointedObject.basedHomMap T
        (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} V) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} T V).inv := by
  change (ihom T).map f ≫ _ = (ihom T).map _ ≫ _
  rw [kanLoopCounit, Functor.map_comp, Category.assoc]
  rfl

namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の構造区間の終点は、符号付き二重随伴を同じ懸垂評価へ施した族そのもの。 -/
lemma kanAdjointStructureCounit_target (n : ℕ) :
    (((φ ≫ kanAdjointParameterLeft X Y n) ≫
      pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n) ≫
      kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space) =
    kanAdjointStructureInput X Y φ n ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (uncurry (KanSequence.signedDoubleAdjoint Y.toKanSequence n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).inv := by
  rw [Category.assoc φ, kanAdjointParameterLeft_step]
  change (kanAdjointStructureInput X Y φ n ≫
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) _) ≫ _ = _
  have hc := kanLoopCounit_post (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint Y.toKanSequence n ≫
      (KanSequence.signedLoopTail Y.toKanSequence).sigma n)
  rw [← KanSequence.uncurry_signedDoubleAdjoint Y.toKanSequence n] at hc
  exact (Category.assoc _ _ _).trans (congrArg (kanAdjointStructureInput X Y φ n ≫ ·) hc)

/-- 始点も同じ普遍懸垂評価へ通常の二重随伴を施した座標へ厳密に一致する。 -/
lemma kanAdjointStructureCounit_source_double (n : ℕ) :
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 2) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (PointedSimplicialSet.circle.{u} ◁ X.sigma n ≫ X.sigma (n + 1))
        (Y.level (n + 2)).space) =
    kanAdjointStructureInput X Y φ n ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (uncurry (KanSequence.ordinaryDoubleAdjoint Y.toKanSequence n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).inv := by
  rw [← kanAdjointStructureCounit_source X Y φ n,
    Category.assoc φ]
  erw [kanAdjointParameterLeft_source_restriction X Y n]
  change (kanAdjointStructureInput X Y φ n ≫
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) _) ≫ _ = _
  have hc := kanLoopCounit_post (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1))
  have hu := congrArg (fun f => uncurry f)
    (KanSequence.ordinaryDoubleAdjoint_eq Y.toKanSequence n)
  rw [uncurry_curry] at hu
  change (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1)) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u}
      (Y.toKanSequence.level (n + 1 + 1)).space = _ at hu
  rw [hu] at hc
  exact (Category.assoc _ _ _).trans (congrArg (kanAdjointStructureInput X Y φ n ≫ ·) hc)

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
