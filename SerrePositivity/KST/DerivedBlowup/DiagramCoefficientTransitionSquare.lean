module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式射に沿う局所制限の指定四角形。
方針：局所 dg 遷移の可換式を標準加群制限・導来制限の合成同型へ移す。
規約：右随伴の二経路を同じ直接制限へ比較する指定経路を使う。
使われ方：canonical な局所加群比較と cartesian 条件の表示変更。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)

/-- 概要：係数成分と局所遷移に沿う加群制限の指定可換四角形。
方針：二経路の合成 dg 関手の等式に標準制限合成同型を適用する。
規約：KST §3.1。使われ方：指定局所加群比較の行先を合わせる。 -/
def diagramCoefficientModuleTransitionIso {i j : J} (h : i ≤ j) :
    moduleRestriction R (AlgebraVertex (F.obj j))ᵒᵖ (AlgebraVertex (G.obj j))ᵒᵖ
        (algebraVertexMap (α.app j)).op.op ⋙
      moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op.op ≅
    moduleRestriction R (AlgebraVertex (G.obj i))ᵒᵖ (AlgebraVertex (G.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition G h).op.op ⋙
      moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (G.obj i))ᵒᵖ
        (algebraVertexMap (α.app i)).op.op :=
  transitionRestrictionCompIso (diagramAlgebraVertexTransition F h) (algebraVertexMap (α.app j))
    ((diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j))) rfl ≪≫
  (transitionRestrictionCompIso (algebraVertexMap (α.app i)) (diagramAlgebraVertexTransition G h)
    ((diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j)))
    (diagramCoefficientDGFunctor_transition α h).symm).symm

/-- 概要：係数成分と局所遷移に沿う導来制限の指定可換四角形。
方針：同じ dg 可換式に、局所化前の指定経路を延長した標準導来合成同型を使う。
規約：KST §3.1・Lemma 3.6。使われ方：導来比較射と随伴の四角形。 -/
def diagramCoefficientDerivedTransitionIso {i j : J} (h : i ≤ j) :
    diagramCoefficientLocalDerivedRestriction α j ⋙ diagramAlgebraDerivedRestriction F h ≅
      diagramAlgebraDerivedRestriction G h ⋙ diagramCoefficientLocalDerivedRestriction α i :=
  transitionDerivedRestrictionCompIso (diagramAlgebraVertexTransition F h)
    (algebraVertexMap (α.app j))
    ((diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j))) rfl ≪≫
  (transitionDerivedRestrictionCompIso (algebraVertexMap (α.app i))
    (diagramAlgebraVertexTransition G h)
    ((diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j)))
    (diagramCoefficientDGFunctor_transition α h).symm).symm

end SerrePositivity.KST.DerivedBlowup
