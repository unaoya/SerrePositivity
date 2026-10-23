module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionShapePushout
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFibration

/-!
概要：底上の単射による切断空間の制限は Kan fibration になる。
方針：底上の前合成を通常の相対前合成と図式の等式による同型へ分解する。
規約：射影の left fibration 性と形状の単射性だけを使う。
使われ方：骨格の押し出しによる切断空間の厳密な引き戻しをホモトピー的比較に使う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E S : SSet.{u}} (q : E ⟶ S) {A B : Over S}

/-- 底上の制限は通常の制限と底の図式の等式による移送の合成。 -/
lemma relativeFunctorOverPre_eq_pre_transport (f : A ⟶ B) :
    relativeFunctorOverPre q f = relativeFunctorPre q B.hom f.left ≫
      eqToHom (congrArg (relativeFunctorSpace q) f.w) := by
  have ht {X : SSet.{u}} {a b : X ⟶ S} (h : a = b) :
      eqToHom (congrArg (relativeFunctorSpace q) h) ≫
        vertexFiberι ((ihom X).map q) (functorVertex b) =
          vertexFiberι ((ihom X).map q) (functorVertex a) := by
    cases h
    exact Category.id_comp _
  apply vertexFiber_hom_ext ((ihom A.left).map q) (functorVertex A.hom)
  rw [Category.assoc, ht f.w, relativeFunctorOverPre_ι, relativeFunctorPre_ι]

/-- left fibration の切断空間は、底上の単射に沿って Kan fibration で制限される。 -/
lemma relativeFunctorOverPre_fibration [LeftFibration q] (f : A ⟶ B) [Mono f.left] :
    Fibration (relativeFunctorOverPre q f) := by
  rw [relativeFunctorOverPre_eq_pre_transport]
  have := relativeFunctorPre_fibration q B.hom f.left
  infer_instance

end
end SerrePositivity.InfinityCategories.HomotopyLimits
