module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafNativeDensityKan
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaLeftKanDensityImage

/-!
概要：専用反映候補は全前層の元の密度余錐を余極限へ送る。
方針：Yoneda 上で可逆な単位から標準余錐の普遍性を取り出し、elements へ制限する。
規約：指定された全余錐と同じ候補関手を保持する。
使われ方：P_Σ 上への制限の回収と反映の余単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {C : SSet.{u}} [Quasicategory C]
    {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)
include β hβ

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    RightFibration (leftKanProjection (yonedaInfinityMap C) v) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    Quasicategory (leftKanShape (yonedaInfinityMap C) v) :=
  quasicategory_of_innerFibration (leftKanProjection (yonedaInfinityMap C) v)

/-- 概要：専用候補の指定 Yoneda 単位は可逆。
方針：元の Yoneda の充満忠実性を元の Kan 単位判定へ渡す。
規約：別の回収同型を選ばず、同じ単位そのものを判定する。
使われ方：標準密度余錐の像の余極限性。 -/
lemma sigmaReflectorLeftKan_unit_isIso :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) :=
  leftKanExtension_unit_isIso_of_fullyFaithful _ (yonedaInfinityMap_isFullyFaithful C) β hβ

/-- 概要：専用候補の全ての元の Yoneda 標準余錐は余極限。
方針：同じ可逆単位を指定変換付き Kan 条件から消去する。
規約：元の候補関手を保持する。
使われ方：小さい elements 上への同値制限。 -/
lemma sigmaReflectorLeftKan_canonicalColimits (v : (PresheafInfinity C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (yonedaInfinityMap C) L v) :=
  F1B.kanLeftKanExtension_canonicalColimits_of_unit_isIso _ β hβ
    (sigmaReflectorLeftKan_unit_isIso β hβ) v

/-- 概要：専用候補は任意の全前層の同じ密度余錐を余極限へ送る。
方針：元の標準余錐を同じ elements 比較で制限する。
規約：全前層を量化し、局所対象に限定しない。
使われ方：P_Σ 上の候補の回収。 -/
lemma sigmaReflectorLeftKan_density_image_isColimit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsColimitCone (mapJoinCocone L (presheafDensityCocone F)) := by
  let c := leftKanCanonicalCocone (yonedaInfinityMap C) L (functorVertex F)
  have hc := (isColimitCone_iff_restrict_equivalentShape (presheafElementsLeftKanComparison F)
    (presheafElementsLeftKanComparison_isQCatEquivalence F) c).mp
      (sigmaReflectorLeftKan_canonicalColimits β hβ _)
  apply (F2.isColimitCone_iff_of_cocone_val_eq (c.restrict _)
    (mapJoinCocone L (presheafDensityCocone F)) ?_).mp hc
  change joinMap _ (𝟙 _) ≫ (_ ≫ L) = _
  rw [← Category.assoc]
  exact congrArg (fun g ↦ g ≫ L) (presheafElementsLeftKanComparison_coconeMap F)

/-- 概要：P_Σ 上への候補の制限は元の全標準密度余錐を保つ。
方針：包含した密度余錐の厳密な等式を全前層での判定へ渡す。
規約：同じ包含と候補の合成を用いる。
使われ方：恒等関手との左 Kan 一意性による余単位の構成。 -/
lemma sigmaReflectorRestriction_canonicalColimits (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C)
      (sigmaPresheafInfinityInclusion C ≫ L) v) := by
  apply (sigmaCanonicalColimits_iff_densityImages (sigmaPresheafInfinityInclusion C ≫ L)).mpr
    (fun w ↦ ?_) v
  apply (F2.isColimitCone_iff_of_cocone_val_eq
    (mapJoinCocone L (presheafDensityCocone (sigmaPresheafVertexFunctor w)))
    (mapJoinCocone (sigmaPresheafInfinityInclusion C ≫ L) (sigmaVertexDensityCocone w)) ?_).mp
      (sigmaReflectorLeftKan_density_image_isColimit β hβ _)
  change _ ≫ L = _ ≫ (_ ≫ L)
  rw [← Category.assoc, sigmaVertexDensityCocone_val_inclusion]

end SerrePositivity.InfinityCategories.F2.Presentable
