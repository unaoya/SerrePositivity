module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFilteredFiberComma
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourceSliceRestriction

/-!
概要：元の fiber の compact comma から第一成分の compact 始域 slice への全射影。
方針：元の全 slice 比較を compact 条件で制限する。
規約：元の全射と指定対象への辺を保持する。
使われ方：成分生成表示への cofinal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact 両成分の対象上の comma の第一成分射影。
方針：元の第一射影の slice 後合成を compact 始域条件へ持ち上げる。
規約：全高次の射影を厳密に保つ。
使われ方：元の第一成分上の cofinal 生成表示。 -/
def componentCompactOverFst (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    componentCompactOver μ p q x ⟶ compactSourceSlice μ (x ≫ pullback.fst p q) :=
  fullSubcomplexLift
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app _ v))
    ((fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v))).ι ≫
      sliceOverPostcomp x (pullback.fst p q)) (fun v ↦ by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (F1B.sliceOverPostcomp_projection x (pullback.fst p q))
        (Opposite.op ⦋0⦌)) v.val
    change Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app _
        ((sliceOverPostcomp x (pullback.fst p q)).app _ v.val))
    exact (congrArg (Compact.IsKappaCompact.{u, u + 1} μ) h).mpr
      (fullSubcomplexOnVertices_vertex v).1)

/-- 概要：compact comma の第一射影は元の全 slice 比較との包含を保つ。
方針：全部分持ち上げの包含公式。
規約：全射の厳密な等式。
使われ方：余錐像と元の第一成分余錐の同定。 -/
lemma componentCompactOverFst_inclusion (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    componentCompactOverFst μ p q x ≫
      (fullSubcomplexOnVertices (sliceOver (x ≫ pullback.fst p q))
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
          ((sliceOverProjection (x ≫ pullback.fst p q)).app _ v))).ι =
      (fullSubcomplexOnVertices (sliceOver x)
        (fun v ↦ ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v))).ι ≫
        sliceOverPostcomp x (pullback.fst p q) :=
  fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable
