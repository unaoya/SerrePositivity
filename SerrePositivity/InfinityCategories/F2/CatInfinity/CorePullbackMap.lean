module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackInvertibleEdges

/-!
概要：引き戻しの core と二つの core の引き戻しの比較射。
方針：順射は二射影の core、逆射は元の引き戻しへの lift を core に持ち上げる。
規約：逆射は一方の関手が inner fibration のときに構成する。
使われ方：Cat_∞ の引き戻し候補の全試験関手 core の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {E F B : SSet.{u}}

/-- 概要：引き戻しの core から二つの core の引き戻しへの標準比較射。
方針：二射影の core 上の作用を組にする。
規約：この順射の構成には充填性を仮定しない。
使われ方：core と引き戻しの交換の標準の向き。 -/
def corePullbackMap (p : E ⟶ B) (q : F ⟶ B) :
    (quasicategoryCore (pullback p q) : SSet.{u}) ⟶
      pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) :=
  pullback.lift (quasicategoryCoreMap (pullback.fst p q))
    (quasicategoryCoreMap (pullback.snd p q)) (by
      change quasicategoryCoreFunctor.map (pullback.fst p q) ≫ quasicategoryCoreFunctor.map p =
        quasicategoryCoreFunctor.map (pullback.snd p q) ≫ quasicategoryCoreFunctor.map q
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- 概要：二つの core の引き戻しを元の単体集合の引き戻しへ送る。
方針：core の包含と二射影を元の引き戻しへ持ち上げる。
規約：両射影の包含との可換性を厳密に保つ。
使われ方：core の比較の逆射の元の単体集合への表示。 -/
def corePullbackUnderlying (p : E ⟶ B) (q : F ⟶ B) :
    pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) ⟶ pullback p q :=
  pullback.lift (pullback.fst _ _ ≫ (quasicategoryCore E).ι)
    (pullback.snd _ _ ≫ (quasicategoryCore F).ι) (by
      rw [Category.assoc, ← quasicategoryCoreMap_ι, ← Category.assoc, pullback.condition,
        Category.assoc, quasicategoryCoreMap_ι]
      rfl)

/-- 概要：二つの core の引き戻しは元の引き戻しの core に写る。
方針：二射影の辺が可逆であることを使い、引き戻し内の辺の可逆性を反映する。
規約：第一関手が inner fibration、三対象が quasicategory であることを使う。
使われ方：core と引き戻しの交換の逆射。 -/
def corePullbackInv [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] :
    pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) ⟶
      (quasicategoryCore (pullback p q) : SSet.{u}) :=
  quasicategoryCoreLift (corePullbackUnderlying p q) (by
    intro s
    apply pullback_isInvertibleEdge_of_projections p q (edgeOfSimplex _)
    · apply (isInvertibleEdge_congr
        (f := edgeOfSimplex (((pullback.fst (quasicategoryCoreMap p)
          (quasicategoryCoreMap q)).app (Opposite.op ⦋1⦌) s).val)) ?_).mpr
      · exact quasicategoryCore_edge ((pullback.fst (quasicategoryCoreMap p)
          (quasicategoryCoreMap q)).app _ s)
      · exact congrArg (fun k : pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) ⟶ E ↦
          k.app (Opposite.op ⦋1⦌) s) (pullback.lift_fst _ _ _)
    · apply (isInvertibleEdge_congr
        (f := edgeOfSimplex (((pullback.snd (quasicategoryCoreMap p)
          (quasicategoryCoreMap q)).app (Opposite.op ⦋1⦌) s).val)) ?_).mpr
      · exact quasicategoryCore_edge ((pullback.snd (quasicategoryCoreMap p)
          (quasicategoryCoreMap q)).app _ s)
      · exact congrArg (fun k : pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) ⟶ F ↦
          k.app (Opposite.op ⦋1⦌) s) (pullback.lift_snd _ _ _))

end SerrePositivity.InfinityCategories.F2
