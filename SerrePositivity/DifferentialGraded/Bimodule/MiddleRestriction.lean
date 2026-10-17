module
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched

/-! # 合成の中間dg圏に沿うbimoduleの二つの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

/-- 中間圏が左側に現れる因子は、既存のdg関手に前合成する。 -/
def leftRestriction (P : Bimodule A B C) : Bimodule A B D := F.comp P

/-- 中間圏が右側に現れる因子は、既存の豊穣制限に後合成する。 -/
def rightRestriction (Q : Bimodule A C E) : Bimodule A D E :=
  Q.comp (dgModuleRestriction A D C F.op)

omit [Small.{u} C] [Small.{u} D] [DGCategory A E] in
lemma leftRestriction_leftAt (P : Bimodule A B C) (b : B) :
    (leftRestriction A B C D F P).leftAt b = F.comp (P.leftAt b) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  change ((F.map x y ≫ P.map (F.obj x) (F.obj y)) ≫ moduleHomπ A B _ _ b) ≫ 𝟙 _ =
    F.map x y ≫ (P.map (F.obj x) (F.obj y) ≫ moduleHomπ A B _ _ b)
  rw [Category.comp_id, Category.assoc]

lemma rightRestriction_leftAt_map (Q : Bimodule A C E) (d : D) (e e' : E) :
    ((rightRestriction A C D E F Q).leftAt d).map e e' =
      (Q.leftAt (F.obj d)).map e e' := by
  change (Q.map e e' ≫ moduleRestrictionHom A D C F.op _ _) ≫ moduleHomπ A D _ _ d =
    Q.map e e' ≫ moduleHomπ A C _ _ (F.obj d)
  rw [Category.assoc, moduleRestrictionHom_π]
  rfl

lemma rightRestriction_leftAction (Q : Bimodule A C E) (d : D) {e e' : E} {p i n : ℤ}
    (g : GradedHom A e e' p) (q : (Q.value (F.obj d) e).X i) (hn : i + p = n) :
    leftAction A ((rightRestriction A C D E F Q).leftAt d) g q hn =
      leftAction A (Q.leftAt (F.obj d)) g q hn :=
  congrArg (fun k => (k.f p g).v i n hn q)
    (rightRestriction_leftAt_map A C D E F Q d e e')

end SerrePositivity.DifferentialGraded.Bimodule
