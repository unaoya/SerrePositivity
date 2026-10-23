module

public import SerrePositivity.InfinityCategories.F1.Coherent.PinchedSource

/-!
概要：右 pinched 単体から旗の解像上の豊穣 Hom への射を作る。
方針：path の前半と後半の分解に豊穣合成の保存を適用し、前半を恒等として消去する。
規約：単体的圏の局所 Kan 性は使わない。
使われ方：Kerodon Proposition 4.6.7.16、写像の普遍性の pinched 単体からの方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：端点を正規化した豊穣関手の作用は単体ごとの豊穣合成を保つ。
方針：三つの対象の等号を消去して豊穣関手の合成則を評価する。
規約：始域の豊穣圏の対象と標的の単体的圏の対象を区別する。
使われ方：Kerodon §2.4.3、旗の分解の評価に対する合成則。 -/
lemma enrichedFunctor_map_comp_normalized {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} A C) (i j k : A) {X Y Z : C}
    (hi : T.obj i = X) (hj : T.obj j = Y) (hk : T.obj k = Z)
    (d : SimplexCategoryᵒᵖ) (P : (i ⟶[SSet] j).obj d) (Q : (j ⟶[SSet] k).obj d) :
    (T.map i k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hk)).app d
      ((eComp SSet i j k).app d (P, Q)) =
      (eComp SSet X Y Z).app d
        ((T.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)).app d P,
         (T.map j k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hj hk)).app d Q) := by
  subst X
  subst Y
  subst Z
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (T.map_comp i j k) d)
    (show ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)).obj d from (P, Q))
  exact h

/-- 概要：右 pinched 単体の旗での評価は旗の引き戻しと整合する。
方針：選択した path を前後に分解し、前半の固定面の作用を豊穣恒等として消去する。
規約：単体の面と退化を任意の単調写像で一括して扱う。
使われ方：Kerodon Proposition 4.6.7.16、評価を単体集合の射にする自然性。 -/
lemma coherentPinchedEvaluate_pullback {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d e : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    coherentPinchedEvaluate τ (F.pullback α) =
      (SimplicialCategory.sHom X Y).map (SimplexCategory.mkHom α).op
        (coherentPinchedEvaluate τ F) := by
  have h := enrichedFunctor_map_comp_normalized τ.val
    (⟨ULift.up F.start.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
    ⟨ULift.up (F.maxAt (α 0)).castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩
    (coherentPinched_sourceObj τ F.start) (coherentPinched_sourceObj τ (F.maxAt (α 0)))
    (coherentPinched_targetObj τ) (Opposite.op ⦋e⦌)
    (F.prefixFlag α) ((F.pullback α).pathFlag)
  change (coherentPinchedHom τ F.start).app (Opposite.op ⦋e⦌)
    ((F.prefixFlag α).prod' ((F.pullback α).pathFlag) ⋙ compFunctor _ _ _) = _ at h
  rw [F.prefixFlag_comp_pullback, coherentPinched_prefixFlag, simplicialHom_id_comp_app] at h
  have hn := NatTrans.naturality_apply (coherentPinchedHom τ F.start)
    (SimplexCategory.mkHom α).op F.pathFlag
  exact h.symm.trans hn

/-- 概要：右 pinched 単体は旗の解像から豊穣 Hom への単体的な射を定める。
方針：旗ごとの評価とその引き戻しの自然性を組み合わせる。
規約：宇宙の持ち上げは旗の単体集合側の ULift を戻すだけ。
使われ方：Kerodon Proposition 4.6.7.16、pinched 単体を補助解像からの写像に変換する。 -/
noncomputable def coherentPinchedFlagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n) :
    coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y where
  app d := ↾fun F ↦ coherentPinchedEvaluate τ F.down
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro F
    exact coherentPinchedEvaluate_pullback τ F.down α.unop.toOrderHom

/-- 概要：比較射から来る pinched 単体の旗の写像は射影の後の Yoneda 射。
方針：旗ごとの最大元による引き戻しの計算を射の等式にする。
規約：coherent Hom の比較射が補助解像の射影の前合成となる向き。
使われ方：Kerodon Proposition 4.6.7.16、写像の普遍性と比較射の可換式。 -/
lemma coherentPinchedFlagMap_comparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    coherentPinchedFlagMap (coherentHomComparisonPinchedSimplex σ) =
      coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  exact coherentPinchedEvaluate_comparison σ F.down

end SerrePositivity.InfinityCategories
