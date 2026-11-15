module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolutionStageFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 本体の同じ半自由分解候補の厳密な関手性

## 概要
元の自由 disk 被覆から始まる同じ可算 kernel cell 列を、実際の射について写す。

## 方針
本体の増大を保つ arrow の射を段階で再帰し、同じ可算列の余極限へ渡す。

## 規約
候補の対象・増大・半自由性・擬同型性は本体のものを再利用する。関手の加法性は要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な余単体的入力の解消。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の同じ可算列を、恒等・合成を保つ関手としてまとめる。 -/
def resolutionDiagramFunctor : ModuleCategory R D ⥤ (ℕ ⥤ ModuleCategory R D) where
  obj M := moduleResolutionDiagram R D M
  map g := resolutionDiagramMap R D g
  map_id M := by
    apply NatTrans.ext
    funext k
    exact congrArg (fun s => s.left) (stageArrowMap_id R D M k)
  map_comp g h := by
    apply NatTrans.ext
    funext k
    exact congrArg (fun s => s.left) (stageArrowMap_comp R D g h k)

/-- 本体の同じ可算余極限の候補を関手としてまとめる。 -/
def candidateFunctor : ModuleCategory R D ⥤ ModuleCategory R D :=
  resolutionDiagramFunctor R D ⋙ colim

/-- 同じ余極限への包含は、実際の射の像と可換である。 -/
@[reassoc] theorem candidateι_map {M N : ModuleCategory R D} (g : M ⟶ N) (k : ℕ) :
    moduleResolutionCandidateι R D M k ≫ (candidateFunctor R D).map g =
      (stageArrowMap R D g k).left ≫ moduleResolutionCandidateι R D N k :=
  colimit.ι_map (resolutionDiagramMap R D g) k

/-- 本体の同じ増大を、同じ候補関手の自然変換としてまとめる。 -/
def candidateAugmentation : candidateFunctor R D ⟶ 𝟭 (ModuleCategory R D) where
  app M := moduleResolutionCandidateπ R D M
  naturality M N g := by
    apply colimit.hom_ext
    intro k
    change moduleResolutionCandidateι R D M k ≫
        ((candidateFunctor R D).map g ≫ moduleResolutionCandidateπ R D N) =
      moduleResolutionCandidateι R D M k ≫ (moduleResolutionCandidateπ R D M ≫ g)
    rw [← Category.assoc, candidateι_map, Category.assoc, moduleResolutionCandidateι_π,
      ← Category.assoc, moduleResolutionCandidateι_π]
    have h := (stageArrowMap R D g k).w
    simpa only [stageArrowMap_right, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using h

/-- この同じ候補の半自由性は本体の既存の定理である。 -/
theorem candidateFunctor_semifree (M : ModuleCategory R D) :
    moduleSemifree R D ((candidateFunctor R D).obj M) := moduleResolutionCandidate_semifree R D M

/-- この同じ増大の擬同型性は本体の既存の定理である。 -/
theorem candidateAugmentation_quasiIso (M : ModuleCategory R D) :
    moduleQuasiIso R D ((candidateAugmentation R D).app M) := moduleResolutionCandidateπ_quasiIso R D M

/-- この同じ増大の次数ごとの全射性も本体の既存の定理である。 -/
theorem candidateAugmentation_surjective (M : ModuleCategory R D) :
    moduleDegreewiseSurjective R D ((candidateAugmentation R D).app M) :=
  moduleResolutionCandidateπ_degreewiseSurjective R D M

end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
