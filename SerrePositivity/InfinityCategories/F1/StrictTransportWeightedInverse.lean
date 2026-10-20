module

public import SerrePositivity.InfinityCategories.F1.CoherentReconstructionNaturalIso

/-!
概要：strict transport の像からの実際の weighted nerve を、同じ分類同値の逆にする。
方針：全空間の復元同型を、strict transport による前合成の充満忠実性で戻す。
規約：逆射を抽象的に選び直さず、元の weighted nerve の写像を保持する。
使われ方：復元 span の逆と反転 unstraightening の同じ比較射の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- strict transport の像から元の left fibrations へ戻す、実際の weighted nerve の写像。 -/
def strictTransportWeightedNerveInfinityMap (C : Type u) [Category.{u} C] :
    StrictTransportDiagramInfinity C ⟶ LeftFibrationInfinity (nerve C) :=
  coherentNerveMap strictTransportKanDiagramEnriched ≫ weightedNerveInfinityMap C

/-- 実際の weighted nerve の後に strict transport を取る往復も全空間で恒等と同型。 -/
def strictTransportWeightedNerveTransportIso (C : Type u) [Category.{u} C] :
    FunctorIso (strictTransportWeightedNerveInfinityMap C ≫ leftStrictTransportInfinityMap C)
      (𝟙 (StrictTransportDiagramInfinity C)) := by
  let e := leftStrictTransportInfinityEquivalence C
  have he : e.hom = leftStrictTransportInfinityMap C := rfl
  have hf := (e.precompose (StrictTransportDiagramInfinity C)).isQCatEquivalence.isFullyFaithful
  apply hf.preimageVertexIso
  change FunctorIso
    (e.hom ≫ strictTransportWeightedNerveInfinityMap C ≫ leftStrictTransportInfinityMap C)
    (e.hom ≫ 𝟙 _)
  rw [he]
  have h := (leftStrictTransportWeightedNerveNaturalIso C).postcomp
    (leftStrictTransportInfinityMap C)
  change FunctorIso (𝟙 _ ≫ leftStrictTransportInfinityMap C)
    ((leftStrictTransportInfinityMap C ≫ strictTransportWeightedNerveInfinityMap C) ≫
      leftStrictTransportInfinityMap C) at h
  simpa only [Category.assoc, Category.id_comp, Category.comp_id] using h.symm

/-- strict transport と実際の weighted nerve を両方向に固定した全空間の同値。 -/
def leftStrictTransportWeightedNerveEquivalence (C : Type u) [Category.{u} C] :
    QCatEquivalence (LeftFibrationInfinity (nerve C)) (StrictTransportDiagramInfinity C) where
  hom := leftStrictTransportInfinityMap C
  inv := strictTransportWeightedNerveInfinityMap C
  homInvIso := (leftStrictTransportWeightedNerveNaturalIso C).symm
  invHomIso := strictTransportWeightedNerveTransportIso C

end SerrePositivity.InfinityCategories
