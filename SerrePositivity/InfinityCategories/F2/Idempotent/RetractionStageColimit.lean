module

public import SerrePositivity.InfinityCategories.F2.Idempotent.RetractionStageExhaustive
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
概要：元の Ret(1) 以後の像の増大列の余極限は、元の強い分裂添字そのもの。
方針：各次数で全被覆性と元の部分複体の包含の単射性を使う。
規約：余極限余錐の各脚は、元の段階の包含そのもの。
使われ方：元の第一段階の包含を各段階包含の無限合成として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の第一段階から始まる像の増大列を、元の包含で結んだ図式。 -/
def retractionStageFunctor : ℕ ⥤ SSet.{u} where
  obj m := (retractionStage (m + 1)).toSSet
  map f := retractionStageMap (Nat.succ_le_succ (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の各段階の包含そのものを脚とする、元の分裂添字への余錐。 -/
def retractionStageCocone : Cocone retractionStageFunctor.{u} where
  pt := SplitShape
  ι :=
    { app m := (retractionStage (m + 1)).ι
      naturality _ _ _ := rfl }

/-- 元の段階の包含余錐は、元の単体集合の余極限余錐。 -/
def retractionStageCocone_isColimit : IsColimit retractionStageCocone.{u} := by
  apply evaluationJointlyReflectsColimits
  intro n
  rcases n with ⟨⟨n⟩⟩
  apply Types.FilteredColimit.isColimitOf'
  · intro F
    exact ⟨n, ⟨F, retractionStage_contains_simplex F⟩, rfl⟩
  · intro m x y h
    change x.val = y.val at h
    obtain rfl := Subtype.ext h
    exact ⟨m, 𝟙 m, rfl⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
