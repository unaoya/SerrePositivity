module
public import Mathlib.CategoryTheory.Grothendieck
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.GrothendieckCommaTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NervePrefixes

/-!
概要：元のGrothendieck射列の初区間を、同じ最終基底のfiberへ送る。
方針：元の最終基底への脚をCostructuredArrowに記録し、既存のtransportを使う。
規約：IS-W2 R03eの前向きの単体の部分。元の基底・fiber対象・射を保持する。
使われ方：Grothendieckのnerveからweighted nerveへの同じprefix係数。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

/-- 元の初区間の添字を、元の射列の添字へ含める。 -/
def grothWeightedPrefixIndex (i : Fin (n+1)) (k : Fin (i.val+1)) : Fin (n+1) :=
  ⟨k.val, lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) i.isLt⟩

/-- 元の各初区間を、元の最終基底への脚の圏へ送る。 -/
def grothWeightedPrefixArrow (i : Fin (n+1)) :
    Fin (i.val+1) ⥤ CostructuredArrow (Grothendieck.forget F) (σ.obj i).base where
  obj k := CostructuredArrow.mk ((σ.map (homOfLE
    (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))).base)
  map {k l} f := CostructuredArrow.homMk
    (σ.map (homOfLE (show grothWeightedPrefixIndex i k ≤ grothWeightedPrefixIndex i l
      from leOfHom f))) (by
        simpa only [Grothendieck.forget_obj, Grothendieck.forget_map, homOfLE_comp, CostructuredArrow.mk_hom_eq_self, CostructuredArrow.mk_left,
          Grothendieck.comp_base] using
          (congrArg (fun a => a.base) (σ.map_comp
            (homOfLE (show grothWeightedPrefixIndex i k ≤ grothWeightedPrefixIndex i l from leOfHom f))
            (homOfLE (show grothWeightedPrefixIndex i l ≤ i from Nat.le_of_lt_succ l.isLt)))).symm)
  map_id k := by
    apply CostructuredArrow.hom_ext
    exact σ.map_id _
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact σ.map_comp _ _

/-- 同じ最終基底のfiberに値を持つ、元の初区間の射列。 -/
def grothWeightedPrefixFiber (i : Fin (n+1)) : Fin (i.val+1) ⥤ F.obj (σ.obj i).base :=
  grothWeightedPrefixArrow F σ i ⋙
    SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport F (σ.obj i).base

/-- prefixの各対象は、元の同じ脚で元のfiber対象を移したもの。 -/
theorem grothWeightedPrefixFiber_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F σ i).obj k =
      (F.map ((σ.map (homOfLE
        (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))).base)).toFunctor.obj
          (σ.obj (grothWeightedPrefixIndex i k)).fiber := rfl

/-- 各prefixの最終対象は、元の同じfiber対象そのもの。 -/
theorem grothWeightedPrefixFiber_last (i : Fin (n+1)) :
    (grothWeightedPrefixFiber F σ i).obj (Fin.last i.val) = (σ.obj i).fiber := by
  rw [grothWeightedPrefixFiber_obj]
  change (F.map (σ.map (𝟙 i)).base).toFunctor.obj (σ.obj i).fiber = _
  rw [σ.map_id, Grothendieck.id_base, F.map_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
