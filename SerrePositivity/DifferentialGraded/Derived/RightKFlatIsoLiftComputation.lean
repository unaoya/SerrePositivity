module
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLift

/-! # 右K-flatモデルから移した自然同型の計算と一意性

## 概要
右K-flatモデルから移した自然同型の計算と一意性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma fullyFaithful_conjugate
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (E : C ⥤ D) (hE : E.FullyFaithful) (R : D ⥤ C) (ε : R ⋙ E ≅ 𝟭 D)
    (G H : D ⥤ T) (τ : E ⋙ G ⟶ E ⋙ H) (X : C) :
    G.map (ε.app (E.obj X)).inv ≫ τ.app (R.obj (E.obj X)) ≫
        H.map (ε.app (E.obj X)).hom = τ.app X := by
  let f : R.obj (E.obj X) ⟶ X := hE.preimage (ε.app (E.obj X)).hom
  have hf : E.map f = (ε.app (E.obj X)).hom := hE.map_preimage _
  have hn := τ.naturality f
  change G.map (E.map f) ≫ τ.app X = τ.app (R.obj (E.obj X)) ≫ H.map (E.map f) at hn
  rw [hf] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]

variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E] (hE : localHomKFlat A E)
  {T : Type z} [Category.{z'} T]
  (G H : DerivedBimoduleCategory A C E ⥤ T)
  (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H)

/-- 全導来圏への移送は、指定置換余単位による局所化上の比較の共役である。 -/
lemma rightKFlatDerivedIsoOfPrecomp_conjugate (Q : DerivedBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app Q =
      G.map ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
        (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app
          ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
        H.map ((rightKFlatReplacementCounitIso A C E hE).app Q).hom := by
  dsimp only [rightKFlatDerivedIsoOfPrecomp, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, whiskerLeft_app, whiskerRight_app]
  simp only [Category.id_comp]
  exact congrArg (fun f => G.map ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
    (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫ f)
    (Category.comp_id (H.map ((rightKFlatReplacementCounitIso A C E hE).app Q).hom))

/-- 右K-flat部分圏の局所化への前合成は元の局所化上の比較を回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_app_inclusion
    (Q : DerivedRightKFlatBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app
        ((rightKFlatDerivedInclusion A C E).obj Q) =
      (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app Q := by
  rw [rightKFlatDerivedIsoOfPrecomp_conjugate]
  exact fullyFaithful_conjugate (rightKFlatDerivedInclusion A C E)
    (rightKFlatDerivedInclusion_fullyFaithful A C E hE) (derivedRightKFlatReplacement A C E hE)
    (rightKFlatReplacementCounitIso A C E hE) G H
    (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom Q

/-- 任意の指定右K-flatモデルで、移送前の自然同型の成分を厳密に回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_hom_app (Q : RightKFlatBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) = e.hom.app Q := by
  have h := rightKFlatDerivedIsoOfPrecomp_app_inclusion A C E hE G H e
    ((rightKFlatToDerived A C E).obj Q)
  refine h.trans ?_
  simp only [rightKFlatLocalizedIsoOfPrecomp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change G.map (𝟙 _) ≫ e.hom.app Q ≫ H.map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Category.comp_id (e.hom.app Q)

/-- 右K-flatモデルへの前合成は、指定した自然同型そのものを回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_precomp :
    Functor.isoWhiskerLeft (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
        (rightKFlatDerivedIsoOfPrecomp A C E hE G H e) = e := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  exact rightKFlatDerivedIsoOfPrecomp_hom_app A C E hE G H e Q

include hE in
/-- 全導来関手の自然変換は、任意の指定右K-flatモデル上の成分で判定できる。 -/
lemma rightKFlatDerivedNatTrans_ext {U V : DerivedBimoduleCategory A C E ⥤ T} {α β : U ⟶ V}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) =
        β.app ((bimoduleToDerived A C E).obj Q.obj)) : α = β := by
  apply bimoduleDerivedNatTrans_ext A C E
  intro M
  let Q := rightKFlatResolutionObj A C E hE M
  let a := rightKFlatResolutionDerivedIso A C E hE M
  apply (cancel_epi (U.map a.hom)).mp
  rw [α.naturality, β.naturality]
  exact congrArg (fun f => f ≫ V.map a.hom) (h Q)

/-- 右K-flatモデルからの移送は恒等自然同型を保つ。 -/
lemma rightKFlatDerivedIsoOfPrecomp_refl (U : DerivedBimoduleCategory A C E ⥤ T) :
    rightKFlatDerivedIsoOfPrecomp A C E hE U U (Iso.refl _) = Iso.refl U := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

/-- 右K-flatモデルからの移送は、指定自然同型の合成を保つ。 -/
lemma rightKFlatDerivedIsoOfPrecomp_trans (U V W : DerivedBimoduleCategory A C E ⥤ T)
    (e₁ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ U ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V)
    (e₂ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ W) :
    rightKFlatDerivedIsoOfPrecomp A C E hE U W (e₁ ≪≫ e₂) =
      rightKFlatDerivedIsoOfPrecomp A C E hE U V e₁ ≪≫
        rightKFlatDerivedIsoOfPrecomp A C E hE V W e₂ := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  simp only [Iso.trans_hom, NatTrans.comp_app, rightKFlatDerivedIsoOfPrecomp_hom_app]

/-- 右K-flatモデルからの移送は、任意の関手への後合成とも可換。 -/
lemma rightKFlatDerivedIsoOfPrecomp_whiskerRight {S : Type*} [Category* S] (K : T ⥤ S) :
    Functor.isoWhiskerRight (rightKFlatDerivedIsoOfPrecomp A C E hE G H e) K =
      rightKFlatDerivedIsoOfPrecomp A C E hE (G ⋙ K) (H ⋙ K)
        (Functor.isoWhiskerRight e K) := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  simp only [Functor.isoWhiskerRight_hom, whiskerRight_app,
    rightKFlatDerivedIsoOfPrecomp_hom_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor
