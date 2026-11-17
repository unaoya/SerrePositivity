module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolutionKernelFunctor

/-!
# 既存の kernel 添付段階と増大の関手性

## 概要
元の kernel 添付の写像錐を、元の cone 関手で可換四角形へ施す。

## 方針
本体の cone の恒等・合成と、標準の包含・零ホモトピーによる増大を使う。

## 規約
段階の対象・包含・増大は本体の同じものを保つ。

## 使われ方
BS 著者版 Lemma 4.22 の既存の同じ半自由分解候補の関手性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の零ホモトピーによる cone の増大は、可換四角形について自然である。 -/
theorem complexConeMap_desc {P Q T P' Q' T' : Complex R}
    (a : P ⟶ Q) (a' : P' ⟶ Q') (q : Q ⟶ T) (q' : Q' ⟶ T')
    (hz : a ≫ q = 0) (hz' : a' ≫ q' = 0)
    (u : P ⟶ P') (v : Q ⟶ Q') (w : T ⟶ T')
    (comm : a ≫ v = u ≫ a') (commq : v ≫ q' = q ≫ w) :
    mappingCone.map a a' u v comm ≫ complexConeDesc a' q' hz' =
      complexConeDesc a q hz ≫ w := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, coneMapCochain_ofHom, Cochain.ofHom_comp]
  apply coneMapCochain_desc
  simpa only [← Cochain.ofHom_comp] using congrArg Cochain.ofHom commq

/-- 元の kernel 添付対象を、同じ cone 関手でまとめる。 -/
abbrev kernelStepFunctor : Arrow (ModuleCategory R D) ⥤ ModuleCategory R D :=
  kernelArrowFunctor R D ⋙ moduleConeFunctor R D

/-- 本体の同じ標準包含は、可換四角形について自然である。 -/
@[reassoc] theorem kernelStepMap_ι {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) :
    moduleKernelCellStepι R D F.hom ≫ (kernelStepFunctor R D).map s =
      s.left ≫ moduleKernelCellStepι R D G.hom :=
  moduleConeMap_inr R D (moduleKernelCellMap R D F.hom) (moduleKernelCellMap R D G.hom)
    (kernelSourceMap R D s) s.left (kernelSourceMap_cell R D s).symm

/-- 本体の同じ増大も、可換四角形について自然である。 -/
@[reassoc] theorem kernelStepMap_π {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) :
    (kernelStepFunctor R D).map s ≫ moduleKernelCellStepπ R D G.hom =
      moduleKernelCellStepπ R D F.hom ≫ s.right := by
  change moduleConeMap R D (moduleKernelCellMap R D F.hom) (moduleKernelCellMap R D G.hom)
      (kernelSourceMap R D s) s.left (kernelSourceMap_cell R D s).symm ≫
        moduleConeDesc R D (moduleKernelCellMap R D G.hom) G.hom (moduleKernelCellMap_comp R D G.hom) =
      moduleConeDesc R D (moduleKernelCellMap R D F.hom) F.hom (moduleKernelCellMap_comp R D F.hom) ≫ s.right
  apply moduleMorphism_ext
  intro x
  simp only [Functor.map_comp, moduleConeMap_eval, moduleConeDesc_eval]
  apply complexConeMap_desc
  simpa only [Functor.map_comp] using congrArg (moduleEvaluation R D x).map s.w

/-- 元の kernel 添付段階の同じ増大を arrow 圏の関手としてまとめる。 -/
def kernelStepArrowFunctor : Arrow (ModuleCategory R D) ⥤ Arrow (ModuleCategory R D) where
  obj F := Arrow.mk (moduleKernelCellStepπ R D F.hom)
  map s := Arrow.homMk ((kernelStepFunctor R D).map s) s.right (kernelStepMap_π R D s)
  map_id F := by
    apply Arrow.hom_ext
    · exact (kernelStepFunctor R D).map_id F
    · rfl
  map_comp s t := by
    apply Arrow.hom_ext
    · exact (kernelStepFunctor R D).map_comp s t
    · rfl

/-- 本体の同じ自由 disk 被覆の増大を arrow 圏の関手としてまとめる。 -/
def diskCoverArrowFunctor : ModuleCategory R D ⥤ Arrow (ModuleCategory R D) where
  obj M := Arrow.mk (moduleDiskCoverπ R D M)
  map g := Arrow.homMk (diskCoverMap R D g) g (diskCoverMap_π R D g)
  map_id M := by
    apply Arrow.hom_ext
    · exact diskCoverMap_id R D M
    · rfl
  map_comp g h := by
    apply Arrow.hom_ext
    · exact diskCoverMap_comp R D g h
    · rfl

end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
