module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom

/-!
概要：内部 Hom の反転同型と指定頂点での評価の一致。
方針：全次数の評価を計算し、元の評価の反転と比較する。
規約：評価点は元の頂点を反転した頂点そのもの。
使われ方：矢印圏の成分ごとの余極限判定の双対化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

/-- 概要：反転した関手の指定頂点での評価は元の評価の反転。
方針：内部 Hom の指数比較と定値単体を全次数で計算する。
規約：K と C の充填性は要求しない。
使われ方：点ごとの極限性を余極限性へ反転する。 -/
lemma oppositeInternalHom_evaluate (K C : SSet.{u}) (k : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) = SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C).hom
  let v := (SSet.unitHomEquiv K.op).symm (SSet.opObjEquiv.symm k)
  have he : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) =
      (λ_ (((ihom K).obj C).op)).inv ≫ (v ▷ (((ihom K).obj C).op)) ≫ uncurry e := by
    calc
      _ = curry (uncurry e) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) := by
        rw [curry_uncurry]
      _ = _ := by
        simpa only [v, Equiv.apply_symm_apply] using
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv (uncurry e) v)
  change e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
  rw [he]
  dsimp only [e]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
