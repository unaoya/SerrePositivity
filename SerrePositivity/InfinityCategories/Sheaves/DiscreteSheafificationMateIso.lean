module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationMate
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible

/-!
概要：指定した単位の式を満たす全 mate は可逆。
方針：同じ通常層化の単位の全円柱とその頂点成分を使う。
  文献対応：HTT 6.2.2.7・5.5.4.15。
使われ方：離散係数の指定層化の全比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma iso_postcomp {A B D : SSet.{u}} {f g : A ⟶ B}
    (k : B ⟶ D) (m : FunctorHom f g) [IsIso m] : IsIso (functorHomPostcomp f g k m) := by
  unfold functorHomPostcomp
  infer_instance

private lemma iso_precomp {A B D : SSet.{u}} {f g : B ⟶ D}
    (k : A ⟶ B) (m : FunctorHom f g) [IsIso m] : IsIso (functorHomPrecomp f g k m) := by
  unfold functorHomPrecomp
  infer_instance

private lemma sheafification_unit_precomp_postcomp_isIso
    {C : Type u} [SmallCategory C] {D : SSet.{u + 1}}
    (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
    (I : D ⟶ PresheafCat C SpaceInfinity.{u}) :
    let X := PresheafCat C SpaceInfinity.{u}
    let L := sheafificationFunctor J hJ
    let u := (Classical.choice hJ).unit
    let uI := functorHomPrecomp (𝟙 X) L I u
    IsIso (functorHomPostcomp I (I ≫ L) L uI) := by
  intro X L u uI
  let r := Classical.choice hJ
  let i := (fullSubcomplexOnVertices X (sheafProperty J)).ι
  let R := r.reflector
  let uR := functorHomPostcomp (𝟙 X) L R u
  letI : IsIso uR := r.adjunction.unit_postcompLeft_isIso
  let uL := functorHomPostcomp (𝟙 X) L L u
  have h : functorHomPostcomp ((𝟙 X) ≫ R) (L ≫ R) i uR = uL :=
    functorHomPostcomp_postcomp (𝟙 X) L R i u
  have h' : IsIso (functorHomPostcomp ((𝟙 X) ≫ R) (L ≫ R) i uR) := iso_postcomp i uR
  letI : IsIso uL := h ▸ h'
  have hpre : IsIso (functorHomPrecomp ((𝟙 X) ≫ L) (L ≫ L) I uL) := iso_precomp I uL
  exact (functorHomPrecomp_postcomp (𝟙 X) L I L u).symm ▸ hpre

/-- 指定した単位の式を満たす全 mate は可逆。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma discreteSheafification_specifiedMate_isIso :
∀ {C : Type u} [SmallCategory C]
 (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
let I := (discretePresheafInclusion C).val
∀ (η : FunctorHom I (nerveMap S ≫ I))
 (hηL : IsIso (functorHomPostcomp I (nerveMap S ≫ I)
   (sheafificationFunctor J hJ) η))
 (m : FunctorHom (I ≫ sheafificationFunctor J hJ) (nerveMap S ≫ I))
 (hm : functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
   (sheafificationFunctor J hJ) I (Classical.choice hJ).unit ≫ m = η),
 IsIso m := by
  intro C hC J hJ S I η hηL m hm
  let X := PresheafCat C SpaceInfinity.{u}
  let L := sheafificationFunctor J hJ
  let T := nerveMap S ≫ I
  let r := Classical.choice hJ
  let u := r.unit
  let uI := functorHomPrecomp (𝟙 X) L I u
  let uT := functorHomPrecomp (𝟙 X) L T u
  let uIL := functorHomPrecomp (𝟙 X) L (I ≫ L) u
  let Lm := functorHomPostcomp (I ≫ L) T L m
  have hLuI := sheafification_unit_precomp_postcomp_isIso J hJ I
  have hcomp : functorHomPostcomp I (I ≫ L) L uI ≫ Lm =
      functorHomPostcomp I T L η :=
    (functorHomPostcomp_comp I (I ≫ L) T L uI m).symm.trans
      (congrArg (fun x : FunctorHom I T => functorHomPostcomp I T L x) hm)
  letI : IsIso (functorHomPostcomp I (I ≫ L) L uI) := hLuI
  have hLm : IsIso Lm := (isIso_comp_left_iff _ _).mp (hcomp.symm ▸ hηL)
  letI : IsIso Lm := hLm
  letI : IsIso uT := sheafification_unit_precomp_local_isIso J hJ T
    (discreteSheafificationTarget_mem J)
  letI : IsIso uIL := sheafification_unit_precomp_local_isIso J hJ (I ≫ L)
    (fun v => r.localization_mem (I.app _ v))
  have he := functorHom_whisker_exchange_typed m u
  rw [functorHom_postcomp_id m] at he
  have hh : m ≫ uT = uIL ≫ Lm := he
  exact (isIso_comp_right_iff m uT).mp (hh.symm ▸ inferInstanceAs (IsIso (uIL ≫ Lm)))

end SerrePositivity.InfinityCategories.Sheaves
