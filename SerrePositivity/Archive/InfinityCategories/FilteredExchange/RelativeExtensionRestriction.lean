module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestrictionCondition

/-!
概要：可換正方形に沿って底と初期値を固定した相対延長空間を制限する。
方針：元の相対前合成を制限後の初期値の fiber へ持ち上げる。
規約：元の全延長を保持。使われ方：比較同型の全空間から各点への輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D A' D' E B : SSet.{u}}
  (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
  (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D) (i' : D' ⟶ A')
  (hs : i' ≫ h = k ≫ i)

/-- 概要：全延長とその初期値を同じ可換正方形で制限する実際の写像。
方針：相対前合成の初期値固定式を fiber の普遍性へ適用。
規約：充填性の仮定なし。使われ方：可縮な延長空間の指定比較の自然性。 -/
def relativeExtensionRestriction :
    relativeFunctorExtensionSpace p b i v hv ⟶
      relativeFunctorExtensionSpace p (h ≫ b) i' (k ≫ v)
        (by rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc]) :=
  vertexFiberLift _ _
    (relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPre p b h) (by
      apply vertexFiber_hom_ext ((ihom D').map p) (functorVertex (i' ≫ h ≫ b))
      change relativeFunctorExtensionSpaceι p b i v hv ≫
        vertexFiberι ((ihom A).map p) (functorVertex b) ≫
          (pre h).app E ≫ (pre i').app E = SSet.const (functorVertex (k ≫ v))
      exact relativeExtensionRestriction_condition p b i v hv h k i' hs)

/-- 概要：延長空間の制限の包含は元の相対前合成そのもの。
方針：fiber への持ち上げの包含式。
規約：射の厳密な等式。使われ方：指定同型の端点評価との照合。 -/
lemma relativeExtensionRestriction_ι :
    relativeExtensionRestriction p b i v hv h k i' hs ≫
      relativeFunctorExtensionSpaceι p (h ≫ b) i' (k ≫ v)
        (by rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc]) =
      relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPre p b h := rfl

/-- 概要：実際の元の延長の制限はその同じ延長を前合成した頂点。
方針：二段の fiber の包含後の関手頂点を計算。
規約：元の全射を保持。使われ方：元の二つの持ち上げの比較の制限。 -/
lemma relativeExtensionRestriction_vertex (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v) :
    (relativeExtensionRestriction p b i v hv h k i' hs).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
        relativeFunctorExtensionSpaceVertexEquiv p (h ≫ b) i' (k ≫ v)
          (by rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc])
          ⟨h ≫ W, by rw [Category.assoc, hW],
            by rw [← Category.assoc, hs, Category.assoc, hWi]⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.F2
