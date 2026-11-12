module
public import SerrePositivity.KST.SConstruction.DGHomGluingFunctor
public import SerrePositivity.KST.SConstruction.DGRepresentableThickGeneration
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations

/-! # 元の Hom gluing の比較辺の実 Perf cone
概要：gluing 対象の元の比較辺を、終域の表現可能加群の標準 cone へ送る。
方針：同じ閉元を閉射へ戻し、元の Yoneda と標準加群 cone を使う。
規約：対象族の構成であり、全 Hom 上の dg 関手化は別工程。
使われ方：対角像の収縮と、具体的 ⊙ から終域への比較射。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 同じ gluing の元の閉元を、元の終域内の閉比較射として読む。 -/
def dgHomGluingTargetMap :
    ForgetEnrichment.of (Complex R) (p.obj X.left) ⟶
      ForgetEnrichment.of (Complex R) (q.obj X.right) :=
  (closedHomEquiv R E (p.obj X.left) (q.obj X.right)).symm X.gluing

/-- 元の閉比較族から作った gluing 対象では、同じ比較射を厳密に回収する。 -/
lemma dgHomGluingTargetMap_comparisonObject
    {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
    (a : ∀ x, ForgetEnrichment.of (Complex R) (p.obj (L.obj x)) ⟶
      ForgetEnrichment.of (Complex R) (q.obj (G.obj x))) (x : P) :
    dgHomGluingTargetMap R C D E p q
      (dgHomGluingComparisonObject R C D E p q L G a x) = a x :=
  (closedHomEquiv R E (p.obj (L.obj x)) (q.obj (G.obj x))).symm_apply_apply (a x)

/-- 元の比較射の、同じ実 Yoneda による加群射。 -/
def dgHomGluingTargetModuleMap :
    ForgetEnrichment.of (Complex R) (representable R (p.obj X.left)) ⟶
      ForgetEnrichment.of (Complex R) (representable R (q.obj X.right)) :=
  (dgYoneda R E).onClosed.map (dgHomGluingTargetMap R C D E p q X)

/-- 元の比較辺の標準加群 cone は実際に射影的 perfect。 -/
def dgHomGluingTargetCone : PerfectDGModule R E :=
  ⟨ForgetEnrichment.to (Complex R)
    (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X)),
    modulePerfectProjectiveOver_cone R E
      ⟨representable_homotopicallyProjective R E (p.obj X.left),
        modulePerfectOver_representable R E (p.obj X.left) (Set.mem_univ _)⟩
      ⟨representable_homotopicallyProjective R E (q.obj X.right),
        modulePerfectOver_representable R E (q.obj X.right) (Set.mem_univ _)⟩
      (dgHomGluingTargetModuleMap R C D E p q X)⟩

/-- 同じ Perf 対象の元の加群は、同じ比較辺の標準 cone そのもの。 -/
lemma dgHomGluingTargetCone_value :
    (dgHomGluingTargetCone R C D E p q X).val =
      ForgetEnrichment.to (Complex R)
        (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X)) := rfl

end SerrePositivity.KST.SConstruction
