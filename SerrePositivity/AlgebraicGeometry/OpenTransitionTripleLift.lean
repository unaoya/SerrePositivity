module

public import SerrePositivity.AlgebraicGeometry.OpenTransitionGlueData

/-!
概要：三重交叉上の射を、開の包含から実際に作る。
方針：開埋め込みの lift とその可換式を、gluing datum の構成に渡す。
規約：残る入力は有限個の開の包含・逆・cocycle の式。
使われ方：G2 の有限段での重なりの模型から実際の gluing datum を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {I : Type u} (U : I → Scheme.{u}) (V : I × I → Scheme.{u})
  (f : ∀ i j, V (i, j) ⟶ U i) [∀ i j, IsOpenImmersion (f i j)]
  (t : ∀ i j, V (i, j) ⟶ V (j, i))
  (hrange : ∀ i j k, Set.range (pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i) ⊆ Set.range (f j k))

include hrange

/-- 三重交叉の実際の射を、開の包含から lift で作る。 -/
def openTransitionTripleLift (i j k : I) : pullback (f i j) (f i k) ⟶ V (j, k) :=
  IsOpenImmersion.lift (f j k) (pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i) (hrange i j k)

/-- lift で作った三重交叉の射の実際の可換式。 -/
@[reassoc (attr := simp)] theorem openTransitionTripleLift_fac (i j k : I) :
    openTransitionTripleLift U V f t hrange i j k ≫ f j k =
      pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i :=
  IsOpenImmersion.lift_fac _ _ _

/-- 開の包含から三重交叉の射を実際に作り、有限個の式で gluing datum にする。 -/
def openTransitionGlueDataOfRange [∀ i, IsIso (f i i)]
    (htid : ∀ i, t i i = 𝟙 _) (hinv : ∀ i j, t i j ≫ t j i = 𝟙 _)
    (hc : ∀ i j k, openTransitionTripleLift U V f t hrange i j k ≫ t j k ≫ f k j =
      pullback.snd (f i j) (f i k) ≫ t i k ≫ f k i) : Scheme.GlueData.{u} :=
  openTransitionGlueData U V f t (openTransitionTripleLift U V f t hrange)
    (openTransitionTripleLift_fac U V f t hrange) htid hinv hc

end SerrePositivity.AlgebraicGeometry
