module

public import SerrePositivity.InfinityCategories.F1.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1.UniversalScaffoldEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorFamilyVertices

/-!
概要：底と初期値を固定する実際の族を、相対延長空間への族へ戻す。
方針：底上で curry した族を、初期制限の fiber へ厳密に持ち上げる。
規約：円柱や高次のパラメータを選び直さず、同じ raw な族を回収する。
使われ方：輸送比較円柱を可縮な延長空間内で比較し、高次の整合性を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 底と初期値を固定するパラメータ族を、同じ相対延長空間への射として表す。 -/
def fixedExtensionCurry {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    L ⟶ relativeFunctorExtensionSpace p β i v hv :=
  vertexFiberLift (relativeFunctorPre p β i) (relativeFunctorVertex p (i ≫ β) v hv)
    (relativeFunctorCurry W hW) (by
      apply relativeFunctorUncurry_injective p (i ≫ β)
      rw [relativeFunctorUncurry_pre, relativeFunctorUncurry_curry, hI]
      change _ = uncurry (SSet.const (relativeFunctorVertex p (i ≫ β) v hv) ≫
        vertexFiberι ((ihom D).map p) (functorVertex (i ≫ β)))
      rw [SSet.const_comp]
      exact (uncurry_const_functorVertex v).symm)

/-- 相対延長空間への持ち上げは、包含後に元の相対 curry そのものになる。 -/
lemma fixedExtensionCurry_ι {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    fixedExtensionCurry p β i v hv W hW hI ≫ relativeFunctorExtensionSpaceι p β i v hv =
      relativeFunctorCurry W hW := by
  dsimp only [fixedExtensionCurry, relativeFunctorExtensionSpaceι]
  rw [vertexFiberLift_ι]

/-- 延長空間へ戻した同じ族を展開すると、元の raw な族を厳密に回収する。 -/
lemma fixedExtensionCurry_uncurry {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    relativeFunctorUncurry
      (fixedExtensionCurry p β i v hv W hW hI ≫ relativeFunctorExtensionSpaceι p β i v hv) =
        W := by
  rw [fixedExtensionCurry_ι, relativeFunctorUncurry_curry]

/-- 延長空間の族をパラメータ頂点で評価すると、同じ頂点で制限した実際の延長になる。 -/
lemma fixedExtensionCurry_vertex {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) (x : L _⦋0⦌) :
    (fixedExtensionCurry p β i v hv W hW hI).app _ x =
      relativeFunctorExtensionSpaceVertexEquiv p β i v hv
        ⟨lift (𝟙 A) (SSet.const x) ≫ W,
          by rw [Category.assoc, hW, ← Category.assoc, lift_fst, Category.id_comp], by
            rw [← Category.assoc, ← parameterVertex_naturality, Category.assoc, hI,
              ← Category.assoc, lift_fst, Category.id_comp]⟩ := by
  apply Subtype.ext
  exact relativeFunctorCurry_vertex p β W hW x

end
end SerrePositivity.InfinityCategories.HomotopyLimits
