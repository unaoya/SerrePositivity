module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeTailExtension

/-!
概要：tail の退化拡張の正頂点間の Hom は、初点固定の添字変換と可換。
方針：path の全点が正であることから、二つの順序写像の像を直接照合する。
規約：拡張全体の自然性を主張しない。
使われ方：始点固定 cone の単体的自然性の正頂点間の分岐。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 正頂点間の Hom に限れば、tail の退化拡張は初点固定の制限と可換。 -/
lemma coherentConeTailExtension_map_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (A : (SimplicialNerve C) _⦋n⦌) (i j : Fin (m + 1)) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).map
        (⟨ULift.up i.succ⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2))))
        ⟨ULift.up j.succ⟩ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension A).map
        ⟨ULift.up (α.toOrderHom i).succ⟩ ⟨ULift.up (α.toOrderHom j).succ⟩ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension ((SimplicialNerve C).map α.op A)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  change (A.map _ _).app d _ = (A.map _ _).app d _
  congr 1
  apply CategoryTheory.Functor.ext (fun l => ?_)
  apply SimplicialThickening.Path.ext
  change (fun k : ULift.{u} (Fin (n + 2)) => ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTailRetraction n k.down)) ''
      ((fun k : ULift.{u} (Fin (m + 2)) =>
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom k.down)) '' (P.obj l).I) =
    (fun k : ULift.{u} (Fin (m + 1)) => ULift.up (α.toOrderHom k.down)) ''
      ((fun k : ULift.{u} (Fin (m + 2)) =>
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTailRetraction m k.down)) '' (P.obj l).I)
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  rintro ⟨k⟩ hk
  induction k using Fin.cases with
  | zero =>
    have h := (P.obj l).left_le _ hk
    change i.succ ≤ 0 at h
    simp at h
  | succ k => rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
