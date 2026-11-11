module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom
public import SerrePositivity.KST.Spectra.FreeActionEndNaturality

/-!
概要：自由 G 軌道の射による関数複体の前合成の具体的な座標式。
方針：各軌道の代表 (1,t) の像の群成分を係数へ作用させ、残りの成分で関数を評価する。
規約：添字集合や群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。群 cochain の顔写像の非斉次座標表示。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G S T : Type u} [Group G]

/-- 概要：自由 G 軌道の間の射が係数の関数複体に誘導する前合成。
方針：軌道代表の像を群成分と添字成分に分けて評価する。
規約：θ は G×T から G×S への同変射。
使われ方：Goerss–Jardine VIII §2。cochain の顔・退化の座標ごとの作用。 -/
def functionPre
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action SSet.{u} G) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S B.V ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj T B.V where
  app n := ↾fun x t ↦
    let p := θ.hom ((1 : G), t)
    (B.ρ p.1).asHom.app n (x p.2)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro x
    change (fun t ↦ (B.ρ (θ.hom ((1 : G), t)).1).asHom.app m
        (B.V.map f (x (θ.hom ((1 : G), t)).2))) =
      fun t ↦ B.V.map f ((B.ρ (θ.hom ((1 : G), t)).1).asHom.app n
        (x (θ.hom ((1 : G), t)).2))
    funext t
    exact congr($((B.ρ (θ.hom ((1 : G), t)).1).asHom.naturality f)
      (x (θ.hom ((1 : G), t)).2))

lemma functionPre_eval
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action SSet.{u} G) (t : T) :
    functionPre θ B ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T B.V t =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S B.V (θ.hom ((1 : G), t)).2 ≫
        (B.ρ (θ.hom ((1 : G), t)).1).asHom := rfl

end

end SerrePositivity.KST.Spectra.FreeActionFamily
