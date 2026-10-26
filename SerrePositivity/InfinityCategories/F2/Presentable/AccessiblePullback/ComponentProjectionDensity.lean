module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AccessibleCompactSourceDensity
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberOverProjection

/-!
概要：compact 成分 comma の射影の cofinal 性を元の成分余極限性へ接続する。
方針：元の accessible 成分の compact 密度余錐を同じ全模型へ制限する。
規約：元の全余錐と元の成分射影を保持する。
使われ方：一般 accessible 引き戻しの compact 成分生成表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：compact 両成分の対象上の comma の第二成分射影。
方針：元の第二射影の slice 後合成を compact 始域条件へ持ち上げる。
規約：全高次の射影を厳密に保つ。
使われ方：元の第二成分上の cofinal 生成表示。 -/
def componentCompactOverSnd (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    componentCompactOver μ p q x ⟶ compactSourceSlice μ (x ≫ pullback.snd p q) :=
  fullSubcomplexLift
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.snd p q)).app _ v))
    ((fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v))).ι ≫
      sliceOverPostcomp x (pullback.snd p q)) (fun v ↦ by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (F1B.sliceOverPostcomp_projection x (pullback.snd p q))
        (Opposite.op ⦋0⦌)) v.val
    change Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.snd p q)).app _
        ((sliceOverPostcomp x (pullback.snd p q)).app _ v.val))
    exact (congrArg (Compact.IsKappaCompact.{u, u + 1} μ) h).mpr
      (fullSubcomplexOnVertices_vertex v).2)

/-- 概要：compact comma の第二射影は元の全 slice 比較との包含を保つ。
方針：全部分持ち上げの包含公式。
規約：全射の厳密な等式。
使われ方：余錐像と元の第二成分余錐の同定。 -/
lemma componentCompactOverSnd_inclusion (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    componentCompactOverSnd μ p q x ≫
      (fullSubcomplexOnVertices (sliceOver (x ≫ pullback.snd p q))
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
          ((sliceOverProjection (x ≫ pullback.snd p q)).app _ v))).ι =
      (fullSubcomplexOnVertices (sliceOver x)
        (fun v ↦ ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v))).ι ≫
        sliceOverPostcomp x (pullback.snd p q) :=
  fullSubcomplexLift_ι _ _ _

/-- 概要：compact 成分 comma の成分射影が cofinal なら元の標準全余錐はその成分で余極限。
方針：同じ compact 密度余錐を成分射影と小さい全同値模型に沿って制限する。
規約：元の全図式と固定対象を保ち、filtered 保存性はまだ不要。
使われ方：両成分での判定による元の引き戻しの生成表示。 -/
lemma componentCanonicalCocone_image_isColimit_of_isRightCofinal
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E D B C : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (hC : IsKappaAccessible μ C) (π : pullback p q ⟶ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    {M : SSet.{u}} [Quasicategory M]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M) (componentCompactOver μ p q x))
    (F : componentCompactOver μ p q x ⟶ compactSourceSlice μ (x ≫ π))
    (hF : F ≫ (fullSubcomplexOnVertices (sliceOver (x ≫ π))
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
          ((sliceOverProjection (x ≫ π)).app (Opposite.op ⦋0⦌) v))).ι =
      (fullSubcomplexOnVertices (sliceOver x)
        (fun v ↦ ComponentCompactVertex μ p q
          ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v))).ι ≫ sliceOverPostcomp x π)
    (hcofinal : IsRightCofinal F) :
    IsColimitCone (mapJoinCocone π (sliceDiagramCocone (e.hom ≫
      (fullSubcomplexOnVertices (sliceOver x) (fun v ↦ ComponentCompactVertex μ p q
        ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v))).ι))) := by
  let j := (fullSubcomplexOnVertices (sliceOver x) (fun v ↦ ComponentCompactVertex μ p q
    ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v))).ι
  let T := e.hom ≫ j
  let c := sliceDiagramCocone T
  let je := (fullSubcomplexOnVertices (sliceOver (x ≫ π))
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ π)).app (Opposite.op ⦋0⦌) v))).ι
  let ce := compactSourceSliceDensityCocone μ (x ≫ π)
  have hce := compactSourceSliceDensityCocone_isColimit_of_isKappaAccessible hμ hC (x ≫ π)
  have hcR : IsColimitCone (ce.restrict F) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal F hcofinal ce).mp hce
  have hcM : IsColimitCone ((ce.restrict F).restrict e.hom) :=
    (Ind.isColimitCone_iff_restrict_equivalentShape e.hom e.isQCatEquivalence _).mp hcR
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hcM
  change joinMap e.hom (𝟙 Δ[0]) ≫
    (joinMap F (𝟙 Δ[0]) ≫ sliceOverUncurry je) = sliceOverUncurry T ≫ π
  rw [← sliceOverUncurry_precomp, ← sliceOverUncurry_precomp, hF,
    ← Category.assoc, sliceOverUncurry_postcomp]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
