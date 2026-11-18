module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.LinearizedSimplexDesc

/-!
# 元の線形化された標準単体の Hom の評価同値

概要：標準単体の自由加群化からの射は、元の単体的加群の同じ次数の元と同値。
方針：恒等単体で評価し、全単体の基底像を自然性で回収する。
規約：既存 linearization と全単体作用素を保持する。
使われ方：実正規化単体の Hom と Dold–Kan Hom の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
variable (A : Type u) [CommRing A]

def linearizedSimplexHomEquiv (M : SimplicialObject (ModuleCat.{u} A)) (n : SimplexCategory) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n) ⟶ M) ≃ M.obj (Opposite.op n) where
  toFun α := α.app (Opposite.op n) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n)
  invFun := _root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M n
  left_inv α := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.free_hom_ext
    intro s
    change (_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M n
      (α.app (Opposite.op n) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n))).app d (ModuleCat.freeMk s) = _
    rw [_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc_apply]
    let g := SSet.stdSimplex.objEquiv s.down
    have h := ConcreteCategory.congr_hom (α.naturality g.op) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n)
    change α.app d ((ModuleCat.free A).map _
      (ModuleCat.freeMk (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n))))) =
        M.map g.op (α.app (Opposite.op n) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n)) at h
    rw [ModuleCat.free_map_apply] at h
    change α.app d (ModuleCat.freeMk (ULift.up
      ((SSet.stdSimplex.obj n).map g.op (SSet.stdSimplex.objEquiv.symm (𝟙 n))))) = _ at h
    rw [SSet.stdSimplex.map_objEquiv_symm, Category.comp_id] at h
    dsimp only [g] at h
    erw [Equiv.symm_apply_apply] at h
    exact h.symm
  right_inv := _root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc_generator A M n

lemma linearizedSimplexHomEquiv_naturality (M : SimplicialObject (ModuleCat.{u} A))
    {n m : SimplexCategory} (f : n ⟶ m)
    (α : (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj m) ⟶ M) :
    _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A M n ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map
      (SSet.stdSimplex.map f) ≫ α) = M.map f.op (_root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A M m α) := by
  obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A M m).symm.surjective α
  rw [Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M m x).app (Opposite.op n)
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map (SSet.stdSimplex.map f)).app (Opposite.op n)
      (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A n)) = _
  change (_root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc A M m x).app (Opposite.op n)
    ((ModuleCat.free A).map _ (ModuleCat.freeMk _)) = _
  rw [ModuleCat.free_map_apply, _root_.SerrePositivity.ComplexLimits.linearizedSimplexDesc_apply]
  change M.map ((𝟙 n) ≫ f).op x = M.map f.op x
  rw [Category.id_comp]

def linearizedSimplexHomIso (M : SimplicialObject (ModuleCat.{u} A)) :
    (SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).op ⋙ yoneda.obj M ≅
      M ⋙ forget (ModuleCat A) :=
  NatIso.ofComponents (fun d => Equiv.toIso (_root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A M d.unop)) (by
    intro d e f
    apply ConcreteCategory.hom_ext
    intro α
    exact _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv_naturality A M f.unop α)

end SerrePositivity.ComplexLimits
