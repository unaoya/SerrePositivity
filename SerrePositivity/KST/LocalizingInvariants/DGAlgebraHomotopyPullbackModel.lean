module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathFunctor

/-!
概要：実 dg cospan に対し、mapping-path 因子分解の実 pullback 模型を構成する。
方針：全射な target 評価の底変更を使い、元の二脚を結ぶ実乗法的経路を保持する。
規約：一般の ∞ 極限の普遍性は未主張。使われ方：Postnikov 拡大の実模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

def algebra : Mon (Complex R) := MonoidPullback.obj (MappingPath.target R f) g

def replacedProjection : algebra R f g ⟶ MappingPath.algebra R f :=
  MonoidPullback.fst (MappingPath.target R f) g

def right : algebra R f g ⟶ C := MonoidPullback.snd (MappingPath.target R f) g

lemma condition : replacedProjection R f g ≫ MappingPath.target R f = right R f g ≫ g :=
  MonoidPullback.condition _ _

def left : algebra R f g ⟶ A := replacedProjection R f g ≫ MappingPath.projection R f

def path : algebra R f g ⟶ Path.algebra R B :=
  replacedProjection R f g ≫ MappingPath.inclusion R f

lemma path_source : path R f g ≫ Path.source R B = left R f g ≫ f := by
  rw [path, left, Category.assoc, MappingPath.condition, Category.assoc]

lemma path_target : path R f g ≫ Path.target R B = right R f g ≫ g := by
  change (replacedProjection R f g ≫ MappingPath.inclusion R f) ≫ Path.target R B = _
  rw [Category.assoc]
  exact condition R f g

def witness : Path.Witness R (left R f g ≫ f) (right R f g ≫ g) where
  hom := path R f g
  source_eq := path_source R f g
  target_eq := path_target R f g

def cone : Limits.PullbackCone (MappingPath.target R f) g := MonoidPullback.cone _ _

def isLimit : Limits.IsLimit (cone R f g) := MonoidPullback.isLimit _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
