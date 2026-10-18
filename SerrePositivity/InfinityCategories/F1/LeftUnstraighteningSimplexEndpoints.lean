module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSimplexLifts
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.LiftEndpoint

/-!
概要：高次の coherent な変換の持ち上げから各頂点での底上の相対関手を取り出す。
方針：相対延長の空間を頂点で制限し、底変換の同型を使って unstraightening 間の射の空間へ送る。
規約：全次元で、選択空間全体を相対写像空間へ写す。
使われ方：Kerodon Corollary 5.6.5.15、unstraightening の高次の変換の選択独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：高次の変換の持ち上げの底を指定頂点で制限すると、元の射影の後のその頂点の図式となる。
方針：単体の prism の頂点の自然性と指定した値の等式を使う。
規約：最初以外の頂点でも同じ計算を使う。
使われ方：Kerodon Corollary 5.6.5.15、高次の持ち上げの終点の底の固定。 -/
lemma leftUnstraighteningSimplexEndpoint_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u}) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G) :
    simplexPrismVertex n i (leftUnstraightening F) ≫
      ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T) = leftUnstraighteningProjection F ≫ G := by
  rw [← Category.assoc, simplexPrismVertex_naturality, Category.assoc, hi]

/-- 概要：高次の変換の持ち上げの選択空間から、各頂点の unstraightening への相対関手の空間への射。
方針：延長の包含、頂点への制限、底の表示の移送、底変換同型の逆射を合成する。
規約：図式の最初の値は F、指定した頂点の値は G とする。
使われ方：Kerodon Corollary 5.6.5.15、高次の選択を底上の写像空間で比較する写像。 -/
noncomputable def leftUnstraighteningSimplexEndpoint {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G) :
    leftUnstraighteningSimplexChoiceSpace F n T h₀ ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) :=
  relativeFunctorExtensionSpaceι pointedSpaceProjection
    ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T)
    (scaffoldFirstVertex n ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F n T h₀) ≫
      relativeFunctorPre pointedSpaceProjection ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T)
        (simplexPrismVertex n i (leftUnstraightening F)) ≫
      eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
        (leftUnstraighteningSimplexEndpoint_projection F G n T i hi)) ≫
      (relativeFunctorBaseChangeIso pointedSpaceProjection G (leftUnstraighteningProjection F)).inv

/-- 概要：高次の変換の任意の二つの持ち上げは、指定頂点で同型な底上の射を与える。
方針：可縮な持ち上げの選択空間の二頂点の同型を評価の射で写す。
規約：指定頂点の unstraightening への相対写像空間内の同型。
使われ方：Kerodon Corollary 5.6.5.15、高次の変換の頂点での選択独立性。 -/
noncomputable def leftUnstraighteningSimplexEndpointIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G)
    (x y : (leftUnstraighteningSimplexChoiceSpace F n T h₀) _⦋0⦌) :
    VertexIso ((leftUnstraighteningSimplexEndpoint F G n T h₀ i hi).app _ x)
      ((leftUnstraighteningSimplexEndpoint F G n T h₀ i hi).app _ y) :=
  VertexIso.map ((leftUnstraighteningSimplexChoiceSpace_isContractibleKan F n T h₀).vertexIso x y)
    (leftUnstraighteningSimplexEndpoint F G n T h₀ i hi)

end SerrePositivity.InfinityCategories
