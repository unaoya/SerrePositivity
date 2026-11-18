module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexFreeAdjunction

/-!
# 持ち上げ標準単体Homの指定恒等生成元の評価

概要：A09の持ち上げ標準単体Hom同型を同じ恒等単体で評価する。
方針：元の宇宙同型とYoneda評価を合成し、指定自由鎖随伴との式を使う。
規約：既存構成の評価・係数移送の法則。新しい同型を選ばない。
使われ方：HA 1.2.4、IS-W2 B02の重み付き切断の成分計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open scoped Simplicial

/-- 概要：指定持ち上げ標準単体Hom同型は同じ恒等生成元の像。
方針：元の標準単体宇宙同型とYoneda評価の定義。
規約：頂点・射を変えない。使われ方：HA 1.2.4 のA09の指定成分の評価。 -/
theorem liftedStandardSimplexHomIso_hom_apply (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f =
      f.app (Opposite.op n) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n))) := rfl

/-- 概要：A09の標準単体Hom評価は元の正規化標準単体Hom同値そのもの。
方針：指定自由随伴の恒等生成元での評価を合成する。
規約：任意可換環と非有界複体。使われ方：HA 1.2.4 のtensor側と実Γの接続。 -/
theorem normalizedSimplexHomEquiv_via_freeAdjunction (A : Type u) [CommRing A]
    (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    (liftedStandardSimplexHomIso ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H)).hom.app (Opposite.op n)
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f) =
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H n f := by
  rw [liftedStandardSimplexHomIso_hom_apply]
  exact normalizedSimplexHomEquiv_freeAdjunction A H n f

/-- 概要：指定Hom評価をYonedaで戻すと元の全標準単体射になる。
方針：元の標準単体宇宙同型の逆射を前合成しYonedaで検出する。
規約：全高次単体の射の等式。使われ方：HA 1.2.4 のA09の全パラメータの照合。 -/
theorem liftedStandardSimplexHomIso_yoneda (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    liftedStandardSimplexIso.{u}.hom.app n ≫
      SSet.yonedaEquiv.symm ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f) =
    f := by
  apply (cancel_epi (liftedStandardSimplexIso.{u}.inv.app n)).mp
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
