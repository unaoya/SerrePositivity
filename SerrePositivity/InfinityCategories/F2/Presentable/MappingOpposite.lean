module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalFunctorOpposite

/-!
概要：元の関手の指定二対象間の写像空間比較は、反転しても同じ同値性を持つ。
方針：両 pinched 模型を共通の区間模型へ戻し、元の反転同型の自然性で比較する。
規約：指定関手・指定二対象を保持。関手全体の充満忠実性を仮定しない。
使われ方：Ind 比較の始域変数での filtered 生成拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 反転した同じ射の同値性は、二重反転の指定同型で元の射へ反映する。 -/
lemma isQCatEquivalence_iff_op {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) : IsQCatEquivalence f ↔ IsQCatEquivalence (SSet.opFunctor.map f) := by
  constructor
  · exact SerrePositivity.InfinityCategories.F1B.isQCatEquivalence_op
  · intro h
    have h₂ := SerrePositivity.InfinityCategories.F1B.isQCatEquivalence_op h
    have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj X) :=
      inferInstanceAs (Quasicategory X.op.op)
    have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj Y) :=
      inferInstanceAs (Quasicategory Y.op.op)
    have : Quasicategory ((𝟭 SSet.{u}).obj X) := inferInstanceAs (Quasicategory X)
    have : Quasicategory ((𝟭 SSet.{u}).obj Y) := inferInstanceAs (Quasicategory Y)
    have hX := (qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app X)).isQCatEquivalence
    have hY := (qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app Y)).isQCatEquivalence
    have hcomp := h₂.comp hY
    change IsQCatEquivalence (SSet.opFunctor.map (SSet.opFunctor.map f) ≫
      (SSet.opFunctorCompOpFunctorIso.app Y).hom) at hcomp
    have hn : SSet.opFunctor.map (SSet.opFunctor.map f) ≫
        (SSet.opFunctorCompOpFunctorIso.app Y).hom =
          (SSet.opFunctorCompOpFunctorIso.app X).hom ≫ f :=
      SSet.opFunctorCompOpFunctorIso.hom.naturality f
    rw [hn] at hcomp
    exact hX.cancel_left hcomp

/-- 区間模型の同じ比較は、元の右 pinched 比較と同じ同値性を持つ。 -/
lemma intervalFunctorMap_equivalence_iff_pinched {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌) :
    IsQCatEquivalence (intervalFunctorMap f x y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap f x y) := by
  constructor
  · exact HomotopyLimits.pinchedHomMap_equivalence_of_intervalFunctorMap f x y
  · intro h
    apply (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).cancel_left
    rw [← pinchedIntervalComparison_naturality]
    exact h.isQCatEquivalence.comp (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y))

/-- 指定二対象間の元の pinchedHomMap の同値性は、反転した同じ比較の同値性と同値。 -/
lemma pinchedHomMap_equivalence_iff_op {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap (SSet.opFunctor.map f)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  rw [← intervalFunctorMap_equivalence_iff_pinched, ← intervalFunctorMap_equivalence_iff_pinched]
  have hs : IsQCatEquivalence (HomotopyLimits.intervalOppositeIso x y).hom :=
    (qCatEquivalenceOfIso (HomotopyLimits.intervalOppositeIso x y)).isQCatEquivalence
  have ht : IsQCatEquivalence (HomotopyLimits.intervalOppositeIso
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).hom :=
    (qCatEquivalenceOfIso (HomotopyLimits.intervalOppositeIso
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y))).isQCatEquivalence
  rw [isQCatEquivalence_iff_op (intervalFunctorMap f x y)]
  constructor
  · intro h
    apply hs.cancel_left
    rw [← HomotopyLimits.intervalOppositeIso_naturality]
    exact h.comp ht
  · intro h
    apply ht.cancel_right
    change IsQCatEquivalence (SSet.opFunctor.map (intervalFunctorMap f x y) ≫
      (HomotopyLimits.intervalOppositeIso (f.app (Opposite.op ⦋0⦌) x)
        (f.app (Opposite.op ⦋0⦌) y)).hom)
    rw [HomotopyLimits.intervalOppositeIso_naturality]
    exact hs.comp h

end SerrePositivity.InfinityCategories.F2.Presentable
