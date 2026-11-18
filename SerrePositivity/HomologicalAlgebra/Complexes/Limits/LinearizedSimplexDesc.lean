module

public import SerrePositivity.EInfinity.BarrattEccles.Normalized
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 元の自由単体的加群の標準単体からの射

概要：単体的加群の元を、同じ線形化された標準単体からの全自然な射にする。
方針：各標準単体の基底像は元の単体作用素による引き戻し。
規約：既存 linearization の宇宙持ち上げを保持する。
使われ方：実正規化単体の Hom の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
variable (A : Type u) [CommRing A]

def linearizedSimplexGenerator (n : SimplexCategory) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n)).obj (Opposite.op n) :=
  ModuleCat.freeMk (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n)))

def linearizedSimplexDesc (M : SimplicialObject (ModuleCat.{u} A)) (n : SimplexCategory)
    (x : M.obj (Opposite.op n)) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n) ⟶ M where
  app d := ModuleCat.freeDesc (↾fun s => M.map (SSet.stdSimplex.objEquiv s.down).op x)
  naturality d e f := by
    apply ModuleCat.free_hom_ext
    intro s
    change ModuleCat.freeDesc _ ((ModuleCat.free A).map _ (ModuleCat.freeMk s)) =
      M.map f (ModuleCat.freeDesc _ (ModuleCat.freeMk s))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change M.map ((SSet.stdSimplex.objEquiv s.down).op ≫ f) x = _
    rw [M.map_comp]
    rfl

lemma linearizedSimplexDesc_apply (M : SimplicialObject (ModuleCat.{u} A)) (n : SimplexCategory)
    (x : M.obj (Opposite.op n)) (d : SimplexCategoryᵒᵖ)
    (s : ULift.{u} ((SSet.stdSimplex.obj n).obj d)) :
    (_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M n x).app d (ModuleCat.freeMk s) =
      M.map (SSet.stdSimplex.objEquiv s.down).op x := ModuleCat.freeDesc_apply _ _

lemma linearizedSimplexDesc_generator (M : SimplicialObject (ModuleCat.{u} A))
    (n : SimplexCategory) (x : M.obj (Opposite.op n)) :
    (_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M n x).app (Opposite.op n) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n) = x := by
  change ModuleCat.freeDesc _ (ModuleCat.freeMk _) = x
  rw [ModuleCat.freeDesc_apply]
  change M.map (𝟙 (Opposite.op n)) x = x
  rw [M.map_id]
  rfl

end SerrePositivity.ComplexLimits
