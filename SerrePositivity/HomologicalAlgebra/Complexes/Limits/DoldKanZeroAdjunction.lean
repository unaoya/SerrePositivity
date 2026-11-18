module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanZeroIso

/-!
# 元の DK 随伴 Hom の零次数の実評価

概要：元の随伴で得た単体的射の零次数像を、元の鎖射の零次数で計算する。
方針：同じ counit の随伴三角形と零次数 Moore 同型の自然性を使う。
規約：元の随伴 Hom 同値・Γ・counit を保つ。
使われ方：実正規化 Hom 同型の零次数成分と元の複体射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]

lemma doldKanAdjunction_zero_eval (W : SimplicialObject (ModuleCat.{u} R))
    (L : ChainComplex (ModuleCat.{u} R) ℕ)
    (f : (normalizedMooreComplex (ModuleCat R)).obj W ⟶ L) :
    (((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).toAdjunction.homEquiv W L) f).app (Opposite.op ⦋0⦌) ≫
      (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso L).hom = (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv ≫ f.f 0 := by
  let e : SimplicialObject (ModuleCat R) ≌ ChainComplex (ModuleCat R) ℕ :=
    Abelian.DoldKan.equivalence
  let g : W ⟶ (Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤
      SimplicialObject (ModuleCat R)).obj L := (e.toAdjunction.homEquiv W L) f
  have h : (normalizedMooreComplex (ModuleCat R)).map g ≫ e.counitIso.hom.app L = f := by
    change (e.toAdjunction.homEquiv W L).symm ((e.toAdjunction.homEquiv W L) f) = f
    exact (e.toAdjunction.homEquiv W L).symm_apply_apply f
  have h₀ := congrArg (fun t => t.f 0) h
  change g.app (Opposite.op ⦋0⦌) ≫
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (Abelian.DoldKan.Γ.obj L)).inv ≫ (e.counitIso.hom.app L).f 0) = _
  rw [← Category.assoc, _root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso_inv_naturality, Category.assoc]
  exact congrArg (fun t => (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv ≫ t) h₀

end SerrePositivity.ComplexLimits
