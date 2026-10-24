module
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：任意のラベル族へ全 Hom 複体を引き戻した dg 圏と評価を構成する。
方針：単位・合成を元の dg 圏からそのまま使い、評価の Hom 作用を恒等にする。
規約：対象値の単射性・Small 性・充満部分集合への置換を必要としない。
使われ方：ラベルを保持する自由表示・cone・反復表示模型の全次数評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {I : Type w} (value : I → D)

@[instance_reducible] def inducedDGCategory : DGCategory A I :=
  ofHomObjects A I (fun x y => homObject A D (value x) (value y))
    (fun x => eId (Complex A) (value x))
    (fun x y z => eComp (Complex A) (value x) (value y) (value z))
    (fun x y => EnrichedCategory.id_comp (value x) (value y))
    (fun x y => EnrichedCategory.comp_id (value x) (value y))
    (fun w x y z => EnrichedCategory.assoc (value w) (value x) (value y) (value z))

def inducedDGEvaluation :
    letI := inducedDGCategory A value
    DGFunctor A I D := by
  letI := inducedDGCategory A value
  exact { obj := value
          map := fun _ _ => 𝟙 _
          map_id := fun _ => by simp; rfl
          map_comp := fun _ _ _ => by simp; rfl }

lemma inducedDGEvaluation_homIso (x y : I) :
    letI := inducedDGCategory A value
    IsIso ((inducedDGEvaluation A value).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

end SerrePositivity.DifferentialGraded
