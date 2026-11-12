module

public import SerrePositivity.KST.Spectra.RawSpectrumParameterHomFamilies
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeUnit

/-!
概要：厳密な cotensor 値の列射から元の全 Hom に戻す操作のパラメータ制限を計算する。
方針：元の段評価と転置の自然性で照合し、単位の場合は単位子の等式を使う。
規約：全列・全単体の等式。使われ方：厳密な区間列の両端を元の全 Hom 内で固定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

/-- 単位からの内部 Hom に値を取る射の転置は、単位評価後の同じ curry'。 -/
lemma PointedMapping.transpose_unit {T V : PointedSimplicialSet.{u}}
    (f : T ⟶ (ihom (𝟙_ PointedSimplicialSet.{u})).obj V) :
    transpose f = curry' (f ≫ (unitIsoSelf (X := V)).hom) := by
  have he : uncurry f = (λ_ T).hom ≫ f ≫ (unitIsoSelf (X := V)).hom := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curry_unit_evaluation (uncurry f)
    rw [curry_uncurry] at h
    rw [h, Iso.hom_inv_id_assoc]
  unfold transpose curry'
  rw [he, ← Category.assoc, ← Category.assoc, braiding_leftUnitor, Category.assoc]

namespace RawSpectrumMapping

/-- 厳密な列射から戻した族の制限は、同じ cotensor 制限を戻した全列族。 -/
lemma parameterFamily_pre (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A B : PointedSimplicialSet.{u}} (j : B ⟶ A)
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y)) :
    j ≫ parameterFamily X Y A f =
      parameterFamily X Y B (f.comp (KanSequence.mappingPre j Y)) := by
  apply pointed_hom_ext X Y
  intro n
  rw [Category.assoc, parameterFamily_evaluation, parameterFamily_evaluation]
  exact (PointedMapping.transpose_pre_inner (f.app n) j).symm

/-- 単位パラメータの族は、同じ列射の元の Hom の点そのもの。 -/
lemma parameterFamily_unit (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping (𝟙_ _) Y)) :
    parameterFamily X Y (𝟙_ _) f = homPoint X Y (f.comp (KanSequence.mappingUnitEvaluation Y)) := by
  apply pointed_hom_ext X Y
  intro n
  rw [parameterFamily_evaluation, homPoint_evaluation]
  exact PointedMapping.transpose_unit (f.app n)

/-- 任意の端点への制限を、元の全 Hom の同じ列射の点として評価する。 -/
lemma parameterFamily_endpoint (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A : PointedSimplicialSet.{u}} (e : 𝟙_ PointedSimplicialSet.{u} ⟶ A)
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y)) :
    e ≫ parameterFamily X Y A f = homPoint X Y
      ((f.comp (KanSequence.mappingPre e Y)).comp (KanSequence.mappingUnitEvaluation Y)) := by
  rw [parameterFamily_pre, parameterFamily_unit]

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
