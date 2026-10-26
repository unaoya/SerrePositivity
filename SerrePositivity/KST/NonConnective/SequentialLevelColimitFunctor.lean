module
public import SerrePositivity.KST.NonConnective.SequentialLevelColimitLaws
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：K-7 の元の逐次段別 BF 余極限を、実射の厳密な関手へ束ねる。
方針：元の実普遍射とその関手則を使い、通常の余極限関手との自然同型を取る。
規約：同じ段別 BF 対象・注入・比較を保持。非連結化候補そのものの厳密関手性とは区別する。
使われ方：e の filtered/逐次交換を実 BF 射で構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 同じ元の段別逐次 BF 余極限の、厳密な実比較を使う関手。 -/
def sequentialLevelColimitFunctor : SpectrumSequence.{u} ⥤ OmegaSpectrum.{u} where
  obj := sequentialLevelColimitSpectrum
  map := sequentialLevelColimitMap
  map_id := sequentialLevelColimitMap_id
  map_comp := sequentialLevelColimitMap_comp

local instance levelFunctorSequentialColimits :
    HasColimitsOfShape SequentialIndex.{u} OmegaSpectrum.{u} where
  has_colimit D := ⟨_, sequentialLevelColimitIsColimit D⟩

/-- 普通の余極限関手との自然同型も、元の全注入を保持する一意比較から取る。 -/
def sequentialLevelColimitFunctorIso :
    (colim : SpectrumSequence.{u} ⥤ OmegaSpectrum.{u}) ≅ sequentialLevelColimitFunctor :=
  NatIso.ofComponents (fun D => (colimit.isColimit D).coconePointUniqueUpToIso
    (sequentialLevelColimitIsColimit D)) (by
    intro D E η
    apply colimit.hom_ext
    intro a
    change colimit.ι D a ≫ colimMap η ≫
        ((colimit.isColimit E).coconePointUniqueUpToIso
          (sequentialLevelColimitIsColimit E)).hom =
      colimit.ι D a ≫ ((colimit.isColimit D).coconePointUniqueUpToIso
        (sequentialLevelColimitIsColimit D)).hom ≫ sequentialLevelColimitMap η
    rw [ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    exact (sequentialLevelColimitMap_fac η a).symm)

/-- 同じ実段別逐次余極限関手は、存在する通常の余極限を保存する。 -/
instance sequentialLevelColimitFunctor_preservesColimitsOfShape
    {J : Type u} [SmallCategory J] :
    PreservesColimitsOfShape J sequentialLevelColimitFunctor.{u} :=
  preservesColimitsOfShape_of_natIso sequentialLevelColimitFunctorIso

end SerrePositivity.KST.NonConnective
