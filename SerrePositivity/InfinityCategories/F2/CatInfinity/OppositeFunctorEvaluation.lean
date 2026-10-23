module

public import SerrePositivity.InfinityCategories.F1.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：反転した関手の指定頂点での評価は元の評価の反転。
方針：内部 Hom の指数比較と定値単体を全次数で計算する。
規約：K と C の充填性は要求しない。
使われ方：点ごとの極限性を余極限性へ反転する。 -/
lemma oppositeInternalHom_evaluate (K C : SSet.{u}) (k : K _⦋0⦌) :
    (HomotopyLimits.oppositeInternalHomIso K C).hom ≫
      evaluateFunctorAt (SSet.opObjEquiv.symm k) = SSet.opFunctor.map (evaluateFunctorAt k) := by
  let e := (HomotopyLimits.oppositeInternalHomIso K C).hom
  let v := (SSet.unitHomEquiv K.op).symm (SSet.opObjEquiv.symm k)
  have he : e ≫ evaluateFunctorAt (SSet.opObjEquiv.symm k) =
      (λ_ (((ihom K).obj C).op)).inv ≫ (v ▷ (((ihom K).obj C).op)) ≫ uncurry e := by
    calc
      _ = curry (uncurry e) ≫ evaluateFunctorAt (SSet.opObjEquiv.symm k) := by
        rw [curry_uncurry]
      _ = _ := by
        simpa only [v, Equiv.apply_symm_apply] using
          (curry_evaluateFunctorAt_unitHomEquiv (uncurry e) v)
  change e ≫ evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
  rw [he]
  dsimp only [e]
  rw [oppositeInternalHomIso_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end SerrePositivity.InfinityCategories.F2
