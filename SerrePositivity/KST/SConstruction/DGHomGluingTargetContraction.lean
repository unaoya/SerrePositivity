module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetComparison

/-! # 同じ実 gluing cone の対象別収縮元
概要：同じ比較同型から得た実 cone の零性を、微分が恒等となる次数 −1 元へ戻す。
方針：D の加群ホモトピー商の等号判定から、同じ cone の実収縮を選ぶ。
規約：各対象の収縮であり、入力関手間の自然な収縮は主張しない。
使われ方：実 dg 商の ContractedFunctor に渡す対象別データ。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

private lemma homotopy_contractingElement_d (K : ModuleCategory R E)
    (h : ModuleHomotopy R E (𝟙 K) 0) :
    (moduleHom R E (ForgetEnrichment.to (Complex R) K)
      (ForgetEnrichment.to (Complex R) K)).d (-1) 0 h.val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (𝟙 K))).val := by
  have hz := moduleHomCycle_zero R E K K
  exact h.property.trans ((congrArg (fun z =>
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (𝟙 K))).val - z) hz).trans
      (sub_zero _))

/-- 元の比較同型から得た、同じ実 cone の恒等と零を結ぶ加群ホモトピー。 -/
def dgHomGluingTargetConeHomotopy
    (e : ForgetEnrichment.of (Complex R) (p.obj X.left) ≅
      ForgetEnrichment.of (Complex R) (q.obj X.right))
    (he : dgHomGluingTargetMap R C D E p q X = e.hom) :
    ModuleHomotopy R E
      (𝟙 (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X))) 0 := by
  apply Classical.choice
  apply (moduleToHomotopy_map_eq_iff R E _ _).1
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (dgHomGluingTargetCone_isZero R C D E p q X e he).eq_of_src _ _

/-- 同じ実 Perf cone の End における、選択した同じ次数 −1 収縮元。 -/
def dgHomGluingTargetConeContractingElement
    (e : ForgetEnrichment.of (Complex R) (p.obj X.left) ≅
      ForgetEnrichment.of (Complex R) (q.obj X.right))
    (he : dgHomGluingTargetMap R C D E p q X = e.hom) :
    GradedHom R (dgHomGluingTargetCone R C D E p q X)
      (dgHomGluingTargetCone R C D E p q X) (-1) :=
  (dgHomGluingTargetConeHomotopy R C D E p q X e he).val

/-- 同じ選択収縮元の微分は、同じ元の実 Perf cone の恒等元そのもの。 -/
lemma dgHomGluingTargetConeContractingElement_d
    (e : ForgetEnrichment.of (Complex R) (p.obj X.left) ≅
      ForgetEnrichment.of (Complex R) (q.obj X.right))
    (he : dgHomGluingTargetMap R C D E p q X = e.hom) :
    (homObject R (PerfectDGModule R E) (dgHomGluingTargetCone R C D E p q X)
      (dgHomGluingTargetCone R C D E p q X)).d (-1) 0
        (dgHomGluingTargetConeContractingElement R C D E p q X e he) =
    (unitElement R (dgHomGluingTargetCone R C D E p q X)).val :=
  homotopy_contractingElement_d R E
    (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X))
    (dgHomGluingTargetConeHomotopy R C D E p q X e he)

end SerrePositivity.KST.SConstruction
