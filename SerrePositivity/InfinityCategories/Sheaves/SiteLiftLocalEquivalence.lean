module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafElementsSiteLift
public import SerrePositivity.InfinityCategories.Sheaves.LocalBijectivityUniverseLift
public import SerrePositivity.InfinityCategories.Sheaves.SetLocalEquivalence
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
概要：元の集合値局所同値を、同じsiteと値の指定された宇宙移送へ送る。
方針：既存のsite同値による局所全単射性の保存と、同じULiftの篩比較を合成する。
規約：HTT 6.2.2.7の集合値部分の既存構成の係数移送の法則。
  Kerodon §7.1（Tag 02H1）。小さい通常のsiteの集合値模型に限る。
使われ方：S8の表現可能値での検出に、元の同じ局所同値の射を渡す。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 同じ元の局所同値は、指定したsiteと値の宇宙移送でも局所同値となる。 -/
lemma isLocalEquivSet_siteLift (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ) :
    IsLocalEquivSet ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J)
      (siteLiftPresheafMap φ) := by
  let d : AsSmall.{u + 1} C ⥤ C := AsSmall.down
  let JA := d.inducedTopology J
  letI : d.IsEquivalence := (AsSmall.equiv (C := C)).isEquivalence_inverse
  obtain ⟨hi, hs⟩ := (isLocalEquivSet_iff_locallyBijective J φ).mp hφ
  letI := hi
  letI := hs
  apply (isLocalEquivSet_iff_locallyBijective JA (siteLiftPresheafMap φ)).mpr
  constructor
  · apply (isLocallyInjective_ulift_iff JA (Functor.whiskerLeft d.op φ)).mpr
    exact CategoryTheory.Presheaf.isLocallyInjective_whisker JA J d φ
  · apply (isLocallySurjective_ulift_iff JA (Functor.whiskerLeft d.op φ)).mpr
    exact CategoryTheory.Presheaf.isLocallySurjective_whisker JA J d φ

end SerrePositivity.InfinityCategories.Sheaves
