module

public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.SquareOpposite
public import SerrePositivity.InfinityCategories.Core.LimitConeExtension

/-!
概要：同値な形状への制限で元の極限錐を判定する。
方針：錐を反転し、既存の全余錐の制限定理を適用して戻す。
規約：元の錐全体と添字写像を保持する。
使われ方：小さい反対密度錐から標準右 Kan 錐への極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：錐の制限と反転は全余錐の射として可換。
方針：join の逆反転の自然性と零単体の標準正規化を使う。
規約：形状と標的は任意。
使われ方：同値な添字による極限性の保存と反映。 -/
lemma reverseCocone_restrict_val {J K X : SSet.{u}} {D : K ⟶ X}
    (c : JoinCone D) (f : J ⟶ K) :
    (c.reverseCocone.restrict (SSet.opFunctor.map f)).val =
      (restrictJoinCone c f).reverseCocone.val := by
  change joinMap _ (𝟙 _) ≫ c.reverseCocone.val = _
  rw [JoinCone.reverseCocone_val, JoinCone.reverseCocone_val]
  change _ = _ ≫ _ ≫ SSet.opFunctor.map (joinMap (𝟙 _) f ≫ c.val)
  rw [CategoryTheory.Functor.map_comp]
  have h := stableJoinReverse_inv_naturality (𝟙 (Δ[0] : SSet.{u})) f
  simp only [CategoryTheory.Functor.map_id] at h
  calc
    _ = joinMap (𝟙 J.op) (stdSimplex.opIso ⦋0⦌).inv ≫
        (joinMap (SSet.opFunctor.map f) (𝟙 (Δ[0] : SSet.{u}).op) ≫
          (stableJoinReverseIso Δ[0] K).inv) ≫ SSet.opFunctor.map c.val := by
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
    _ = _ := by rw [h]; simp only [Category.assoc]

/-- 概要：同値な添字への制限は指定した極限錐の普遍性を保ち反映する。
方針：反対写像の同値性を全余錐の制限定理へ渡す。
規約：単射性を要求せず、元の全錐を使う。
使われ方：反対密度による右 Kan の局所極限判定。 -/
lemma isLimitCone_iff_restrict_equivalentShape {J K X : SSet.{u}}
    [Quasicategory J] [Quasicategory K] [Quasicategory X]
    (f : J ⟶ K) (hf : IsQCatEquivalence f) {D : K ⟶ X} (c : JoinCone D) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c f) := by
  rw [isLimitCone_iff_reverseCocone c, isLimitCone_iff_reverseCocone (restrictJoinCone c f)]
  exact (Ind.isColimitCone_iff_restrict_equivalentShape _ hf.opposite c.reverseCocone).trans
    (F2.isColimitCone_iff_of_cocone_val_eq _ _ (reverseCocone_restrict_val c f))

end SerrePositivity.InfinityCategories.F2.Presentable
