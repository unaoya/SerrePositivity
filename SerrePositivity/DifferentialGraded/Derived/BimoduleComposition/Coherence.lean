module

public import Mathlib.CategoryTheory.Functor.Currying
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.DifferentialGraded.Derived.KFlat

/-!
# Derived.BimoduleComposition.Coherence

## 概要
指定 K-flat 代表の結合比較、三角・五角 coherence とパラメータ族をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## CompositionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/CompositionFamilies.lean） -/

/-! # dg合成の自然性に使用するパラメータ付き関手合成

## 概要
dg合成の自然性に使用するパラメータ付き関手合成。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionFamilies.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionFamilies
universe u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable {T : Type u₀} [Category.{v₀} T] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

def compositionFamily (F : T ⥤ C ⥤ D) (G : T ⥤ D ⥤ E) : T ⥤ C ⥤ E :=
  F.prod' G ⋙ uncurry.obj (whiskeringLeft C D E)

def compositionFamilyMap {F F' : T ⥤ C ⥤ D} {G G' : T ⥤ D ⥤ E}
    (a : F ⟶ F') (b : G ⟶ G') : compositionFamily F G ⟶ compositionFamily F' G' :=
  whiskerRight (NatTrans.prod' a b) (uncurry.obj (whiskeringLeft C D E))

variable {H : Type u₄} [Category.{v₄} H]

def compositionFamilyAssociator (F : T ⥤ C ⥤ D) (G : T ⥤ D ⥤ E)
    (K : T ⥤ E ⥤ H) :
    compositionFamily (compositionFamily F G) K ≅ compositionFamily F (compositionFamily G K) :=
  NatIso.ofComponents (fun t => Functor.associator (F.obj t) (G.obj t) (K.obj t))
    (fun f => by
      ext X
      dsimp [compositionFamily, uncurry, whiskeringLeft, whiskerLeft]
      simp only [CategoryTheory.Functor.map_comp, Category.id_comp, Category.comp_id,
        Category.assoc])

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end CompositionFamilies

/-! ## BimoduleCompositionAssociatorIndependence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorIndependence.lean） -/

/-! # 全導来結合同型の任意解像度計算と選択独立性

## 概要
全導来結合同型の任意解像度計算と選択独立性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorKFlat.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorIndependence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleAssociatorBaseIso_resolution (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom := by
  let s : rightKFlatResolutionObj A C E hE Q ⟶ S :=
    ⟨bimoduleCanonicalResolutionLift A C E q hq⟩
  let t : rightKFlatResolutionObj A E F hF R ⟶ T :=
    ⟨bimoduleCanonicalResolutionLift A E F r hr⟩
  have h := derivedBimoduleAssociatorResolutionIso_naturality A B C E F hE hF
    (rightKFlatResolutionObj A C E hE Q) S (rightKFlatResolutionObj A E F hF R) T
    (bimoduleCanonicalSemifreeResolution A C E Q).π q
    (bimoduleCanonicalSemifreeResolution A E F R).π r
    (bimoduleCanonicalSemifreeResolution A C E Q).quasiIso hq
    (bimoduleCanonicalSemifreeResolution A E F R).quasiIso hr (𝟙 Q) (𝟙 R) s t
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      (bimoduleCanonicalResolutionLift_fac A C E q hq).symm)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      (bimoduleCanonicalResolutionLift_fac A E F r hr).symm)
  simpa only [derivedBimoduleAssociatorBaseIso, derivedBimoduleComposePairMap,
    derivedBimoduleComposeInnerMap,
    CategoryTheory.Functor.map_id, whiskerRight_id', whiskerLeft_id',
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h.symm

/-- 全因子に自然な結合同型は、任意の指定右K-flat解像度で計算できる。 -/
lemma derivedBimoduleAssociatorIso_resolution_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom :=
  (derivedBimoduleAssociatorIso_base_app A B C E F hE hF Q R).trans
    (derivedBimoduleAssociatorBaseIso_resolution A B C E F hE hF Q R S T q r hq hr)

lemma derivedBimoduleAssociatorIso_resolution_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom ≫
        (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom =
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  rw [derivedBimoduleAssociatorIso_resolution_app, derivedBimoduleAssociatorResolutionIso_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorIndependence

/-! ## BimoduleCompositionAssociatorKFlat（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorKFlat.lean） -/

/-! # 全導来結合同型と既存K-flat結合同型の比較図式

## 概要
全導来結合同型と既存K-flat結合同型の比較図式。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorComponents.lean、
Derived/BimoduleCompositionTriangle.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorKFlat
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleComposePairResolutionIso_self (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposePairResolutionIso A B C E F hE hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S)
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≪≫
        isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
          (derivedBimoduleComposeKFlatIso A B E F hF T) := by
  unfold derivedBimoduleComposePairResolutionIso
  rw [derivedBimoduleComposeResolutionComputation_self,
    derivedBimoduleComposeResolutionComputation_self]

lemma derivedBimoduleComposeInnerResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeInnerResolutionIso A C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj := by
  have hi : bimoduleDerivedIso A C E (𝟙 S.obj)
      ((BimoduleCategory.quasiIso A C E).id_mem S.obj) = Iso.refl _ := by
    apply Iso.ext
    exact (bimoduleToDerived A C E).map_id _
  apply Iso.ext
  change (derivedBimoduleComposeResolutionComputation A C E F hF T.obj T (𝟙 T.obj)
      ((BimoduleCategory.quasiIso A E F).id_mem T.obj)).hom.app
        ((bimoduleToDerived A C E).obj S.obj) ≫
      (derivedComposeWith A C E F T.obj T.property).map
        (bimoduleDerivedIso A C E (𝟙 S.obj)
          ((BimoduleCategory.quasiIso A C E).id_mem S.obj)).inv = _
  rw [hi, Iso.refl_inv, derivedBimoduleComposeResolutionComputation_self,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

lemma derivedBimoduleComposeNestedResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeNestedResolutionIso A B C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      (derivedBimoduleComposeFunctor A B C F hF).mapIso
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj) ≪≫
        derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T) := by
  unfold derivedBimoduleComposeNestedResolutionIso
  rw [derivedBimoduleComposeInnerResolutionIso_self]

lemma derivedBimoduleAssociatorIso_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
        ((bimoduleToDerived A E F).obj T.obj)).app ((bimoduleToDerived A C E).obj S.obj)).hom ≫
      ((derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj).hom ≫
        (derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)).hom) =
    (whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S).hom
        ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≫
      whiskerLeft (derivedComposeWith A B C E S.obj S.property)
        (derivedBimoduleComposeKFlatIso A B E F hF T).hom) ≫
      (rightKFlatDerivedAssociator A B C E F S T).hom := by
  have h := derivedBimoduleAssociatorIso_resolution_fac A B C E F hE hF S.obj T.obj S T
    (𝟙 S.obj) (𝟙 T.obj) ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
    ((BimoduleCategory.quasiIso A E F).id_mem T.obj)
  rw [derivedBimoduleComposePairResolutionIso_self,
    derivedBimoduleComposeNestedResolutionIso_self] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorKFlat

/-! ## BimoduleCompositionAssociatorComponents（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorComponents.lean） -/

/-! # 全導来結合同型の成分と二つの後因子に関する同時自然性

## 概要
全導来結合同型の成分と二つの後因子に関する同時自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorComparison.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorComponents
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 任意の二つの導来後因子で評価した、前因子全体に自然な結合同型。 -/
def derivedBimoduleAssociator (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) :=
  ((derivedBimoduleAssociatorIso A B C E F hE hF).app R).app Q

lemma derivedBimoduleAssociator_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q Q' : DerivedBimoduleCategory A C E}
    {R R' : DerivedBimoduleCategory A E F} (f : Q ⟶ Q') (g : R ⟶ R') :
    derivedBimoduleComposePairMap A B C E F hE hF f g ≫
        (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
      (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeInnerMap A C E F hF f g) := by
  have hQ := ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).naturality f
  have hR := NatTrans.congr_app
    ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.naturality g) Q'
  change whiskerRight ((derivedBimoduleComposeFunctor A B C E hE).map f)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R).hom =
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).map f) at hQ
  change whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q')
      ((derivedBimoduleComposeFunctor A B E F hF).map g) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
    (derivedBimoduleAssociator A B C E F hE hF Q' R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).map g).app Q') at hR
  change (_ ≫ _) ≫ _ = _ ≫ (derivedBimoduleComposeFunctor A B C F hF).map (_ ≫ _)
  rw [Category.assoc, hR, ← Category.assoc, hQ, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorComponents

/-! ## BimoduleCompositionAssociatorComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorComparison.lean） -/

/-! # 導来同型で指定されたK-flat代表と結合同型の比較

## 概要
導来同型で指定されたK-flat代表と結合同型の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonPaths.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorComparison
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleComposePairComparisonIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q : DerivedBimoduleCategory A C E}
    {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ≅
      derivedComposeWith A B C E S.obj S.property ⋙
        derivedComposeWith A B E F T.obj T.property :=
  isoWhiskerRight ((derivedBimoduleComposeFunctor A B C E hE).mapIso q)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≪≫
    isoWhiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj S.obj))
      ((derivedBimoduleComposeFunctor A B E F hF).mapIso r) ≪≫
    isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S)
      ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≪≫
    isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
      (derivedBimoduleComposeKFlatIso A B E F hF T)

def derivedBimoduleComposeInnerComparisonIso (hF : localHomKFlat A F)
    {Q : DerivedBimoduleCategory A C E} {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    ((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q ≅
      (bimoduleToDerived A C F).obj (rightKFlatCompose A C E F S T).obj :=
  ((derivedBimoduleComposeFunctor A C E F hF).obj R).mapIso q ≪≫
    ((derivedBimoduleComposeFunctor A C E F hF).mapIso r).app
      ((bimoduleToDerived A C E).obj S.obj) ≪≫
    derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj

def derivedBimoduleComposeNestedComparisonIso (hF : localHomKFlat A F)
    {Q : DerivedBimoduleCategory A C E} {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) ≅
      derivedComposeWith A B C F (rightKFlatCompose A C E F S T).obj
        (rightKFlatCompose A C E F S T).property :=
  (derivedBimoduleComposeFunctor A B C F hF).mapIso
      (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r) ≪≫
    derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)

lemma derivedBimoduleAssociator_comparison_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q : DerivedBimoduleCategory A C E}
    {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeNestedComparisonIso A B C E F hF S T q r).hom =
      (derivedBimoduleComposePairComparisonIso A B C E F hE hF S T q r).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  have hn := derivedBimoduleAssociator_naturality A B C E F hE hF q.hom r.hom
  have hk := derivedBimoduleAssociatorIso_kFlat_fac A B C E F hE hF S T
  change (derivedBimoduleAssociator A B C E F hE hF _ _).hom ≫ _ = _ at hk
  have hi : (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r).hom =
      derivedBimoduleComposeInnerMap A C E F hF q.hom r.hom ≫
        (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj).hom := by
    exact (Category.assoc _ _ _).symm
  change _ ≫ ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r).hom ≫ _) = _
  rw [hi]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [hk]
  simp only [derivedBimoduleComposePairMap, derivedBimoduleComposePairComparisonIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorComparison

/-! ## BimoduleCompositionTriangle（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionTriangle.lean） -/

/-! # 全導来合成の三角恒等式のK-flat因子での比較

## 概要
全導来合成の三角恒等式のK-flat因子での比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionTriangleFamily.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionTriangle
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma derivedBimoduleTriangle_kFlat (hC : localHomKFlat A C) (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) :
    (((derivedBimoduleAssociatorIso A B C C E hC hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)).hom ≫
      (derivedBimoduleComposeFunctor A B C E hE).map
        ((derivedBimoduleLeftUnitIso A C E hE).hom.app ((bimoduleToDerived A C E).obj Q.obj)) =
    whiskerRight (derivedBimoduleRightUnitIso A B C hC).hom
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (Functor.leftUnitor ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))).hom := by
  let Δ := rightKFlatDiagonal A C
  let U := rightKFlatCompose A C C E Δ Q
  let u : U ⟶ Q :=
    ⟨(leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q.obj)).hom⟩
  have hn := derivedBimoduleComposeKFlatIso_naturality A B C E hE u
  have ha := derivedBimoduleAssociatorIso_kFlat_fac A B C C E hC hE Δ Q
  have ht := derivedTriangle A B C E Q.obj Q.property
  change (rightKFlatDerivedAssociator A B C C E Δ Q).hom ≫
    derivedComposeWithMap A B C E U.property Q.property u.hom = _ at ht
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatIso A B C E hE Q)).1
  rw [derivedBimoduleLeftUnitIso_kFlat_base_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hn]
  simp only [← Category.assoc] at ha ⊢
  rw [ha]
  simp only [Category.assoc]
  rw [ht]
  ext P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.leftUnitor_hom_app,
    ]
  have hx := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom.naturality
    ((derivedRightUnitIso A B C).hom.app P)
  let FQ := (derivedBimoduleComposeFunctor A B C E hE).obj
    ((bimoduleToDerived A C E).obj Q.obj)
  let KQ := derivedComposeWith A B C E Q.obj Q.property
  let c := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom
  let a := (derivedBimoduleComposeKFlatIso A B C C hC Δ).hom.app P
  let r := (derivedRightUnitIso A B C).hom.app P
  change FQ.map a ≫ (c.app _ ≫ (KQ.map r ≫ 𝟙 (KQ.obj P))) =
    FQ.map ((derivedBimoduleRightUnitIso A B C hC).hom.app P) ≫
      (𝟙 (FQ.obj P) ≫ c.app P)
  change FQ.map r ≫ c.app P = c.app _ ≫ KQ.map r at hx
  calc
    _ = FQ.map a ≫ (c.app _ ≫ KQ.map r) :=
      congrArg (fun k => FQ.map a ≫ (c.app _ ≫ k)) (Category.comp_id (KQ.map r))
    _ = FQ.map a ≫ (FQ.map r ≫ c.app P) := congrArg (fun k => FQ.map a ≫ k) hx.symm
    _ = (FQ.map a ≫ FQ.map r) ≫ c.app P := (Category.assoc _ _ _).symm
    _ = FQ.map (a ≫ r) ≫ c.app P := congrArg (fun k => k ≫ c.app P) (FQ.map_comp a r).symm
    _ = _ := (congrArg (fun k => FQ.map (a ≫ r) ≫ k) (Category.id_comp (c.app P))).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionTriangle

/-! ## BimoduleCompositionTriangleFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionTriangleFamily.lean） -/

/-! # 三角恒等式の両経路を束ねる全導来自然変換

## 概要
三角恒等式の両経路を束ねる全導来自然変換。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleLocal.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionTriangleFamily
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

def derivedBimoduleTriangleSource (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    DerivedBimoduleCategory A C E ⥤
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringLeft (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B C)
      (DerivedBimoduleCategory A B E)).obj
        ((derivedBimoduleComposeFunctor A B C C hC).obj
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj))

def derivedBimoduleTriangleLeft (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleSource A B C E hC hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerRight (derivedBimoduleAssociatorIso A B C C E hC hE).hom
      ((CategoryTheory.evaluation (DerivedBimoduleCategory A C C)
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)).obj
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)) ≫
    whiskerRight (derivedBimoduleLeftUnitIso A C E hE).hom
      (derivedBimoduleComposeFunctor A B C E hE)

def derivedBimoduleTriangleRight (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleSource A B C E hC hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerLeft (derivedBimoduleComposeFunctor A B C E hE)
    ((whiskeringLeft (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B C)
      (DerivedBimoduleCategory A B E)).map (derivedBimoduleRightUnitIso A B C hC).hom)

lemma derivedBimoduleTriangleFamily_kFlat (hC : localHomKFlat A C)
    (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleTriangleLeft A B C E hC hE).app ((bimoduleToDerived A C E).obj Q.obj) =
      (derivedBimoduleTriangleRight A B C E hC hE).app ((bimoduleToDerived A C E).obj Q.obj) := by
  have h := derivedBimoduleTriangle_kFlat A B C E hC hE Q
  ext P
  have hp := NatTrans.congr_app h P
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app] at hp
  change _ ≫ _ = _ ≫ 𝟙 _ at hp
  exact hp.trans (Category.comp_id _)

/-- 三角図式は後因子の全指定局所化上の自然変換として可換。 -/
lemma derivedBimoduleTriangle (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleLeft A B C E hC hE =
      derivedBimoduleTriangleRight A B C E hC hE := by
  let J := rightKFlatDerivedInclusion A C E
  let : J.EssSurj := rightKFlatDerivedInclusion_essSurj A C E hE
  have hJ : whiskerLeft J (derivedBimoduleTriangleLeft A B C E hC hE) =
      whiskerLeft J (derivedBimoduleTriangleRight A B C E hC hE) := by
    apply Localization.natTrans_ext (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    intro Q
    exact derivedBimoduleTriangleFamily_kFlat A B C E hC hE Q
  apply NatTrans.ext
  funext Q
  let e := J.objObjPreimageIso Q
  have hx := NatTrans.congr_app hJ (J.objPreimage Q)
  change (derivedBimoduleTriangleLeft A B C E hC hE).app (J.obj (J.objPreimage Q)) =
    (derivedBimoduleTriangleRight A B C E hC hE).app (J.obj (J.objPreimage Q)) at hx
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleTriangleSource A B C E hC hE).mapIso e) _ _).1
  change (derivedBimoduleTriangleSource A B C E hC hE).map e.hom ≫ _ =
    (derivedBimoduleTriangleSource A B C E hC hE).map e.hom ≫ _
  rw [(derivedBimoduleTriangleLeft A B C E hC hE).naturality,
    (derivedBimoduleTriangleRight A B C E hC hE).naturality, hx]

/-- 任意の導来後因子について、結合比較と左単位の経路は右単位の経路に一致する。 -/
lemma derivedBimoduleTriangle_app (hC : localHomKFlat A C) (hE : localHomKFlat A E)
    (Q : DerivedBimoduleCategory A C E) :
    (((derivedBimoduleAssociatorIso A B C C E hC hE).app Q).app
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)).hom ≫
      (derivedBimoduleComposeFunctor A B C E hE).map
        ((derivedBimoduleLeftUnitIso A C E hE).hom.app Q) =
    whiskerRight (derivedBimoduleRightUnitIso A B C hC).hom
      ((derivedBimoduleComposeFunctor A B C E hE).obj Q) :=
  NatTrans.congr_app (derivedBimoduleTriangle A B C E hC hE) Q

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionTriangleFamily

/-! ## BimoduleCompositionPentagonPaths（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonPaths.lean） -/

/-! # 全導来bimodule合成の五角図式の両経路

## 概要
全導来bimodule合成の五角図式の両経路。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonInner.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonPaths
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
  (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
  (S : DerivedBimoduleCategory A F G)

def derivedBimodulePentagonShort :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
      (derivedBimoduleAssociator A B E F G hF hG R S).hom ≫
    (derivedBimoduleAssociator A B C E G hE hG Q
      (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).hom

def derivedBimodulePentagonLong :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerRight (derivedBimoduleAssociator A B C E F hE hF Q R).hom
      ((derivedBimoduleComposeFunctor A B F G hG).obj S) ≫
    (derivedBimoduleAssociator A B C F G hF hG
      (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) S).hom ≫
    (derivedBimoduleComposeFunctor A B C G hG).map
      ((derivedBimoduleAssociator A C E F G hF hG R S).hom.app Q)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonPaths

/-! ## BimoduleCompositionPentagonInner（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonInner.lean） -/

/-! # 五角図式の内側の結合射とK-flat三因子の値比較

## 概要
五角図式の内側の結合射とK-flat三因子の値比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonComparison.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonInner
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w) (F : Type z) (G : Type t)
  [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

def derivedBimoduleTripleLeftValueIso (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    ((derivedBimoduleComposeFunctor A C F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R.obj)).obj ((bimoduleToDerived A C E).obj Q.obj)) ≅
      (bimoduleToDerived A C G).obj
        (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S).obj :=
  derivedBimoduleComposeInnerComparisonIso A C F G hG (rightKFlatCompose A C E F Q R) S
    (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)

def derivedBimoduleTripleRightValueIso (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    ((derivedBimoduleComposeFunctor A C E G hG).obj
        (((derivedBimoduleComposeFunctor A E F G hG).obj
          ((bimoduleToDerived A F G).obj S.obj)).obj ((bimoduleToDerived A E F).obj R.obj))).obj
            ((bimoduleToDerived A C E).obj Q.obj) ≅
      (bimoduleToDerived A C G).obj
        (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S)).obj :=
  derivedBimoduleComposeInnerComparisonIso A C E G hG Q (rightKFlatCompose A E F G R S)
    (Iso.refl _) (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)

lemma derivedBimoduleTripleValueIso_associator (hF : localHomKFlat A F)
    (hG : localHomKFlat A G) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleAssociator A C E F G hF hG
        ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
          ((bimoduleToDerived A C E).obj Q.obj) ≫
        (derivedBimoduleTripleRightValueIso A C E F G hG Q R S).hom =
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S).hom ≫
        (bimoduleToDerived A C G).map
          (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
            (BimoduleCategory.underlying A E F R.obj)
            (BimoduleCategory.underlying A F G S.obj)).hom := by
  have h := NatTrans.congr_app (derivedBimoduleAssociatorIso_kFlat_fac A C E F G hF hG R S)
    ((bimoduleToDerived A C E).obj Q.obj)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    rightKFlatDerivedAssociator_base_app] at h
  simp only [derivedBimoduleAssociator, derivedBimoduleComposeKFlatValueIso,
    derivedBimoduleTripleLeftValueIso, derivedBimoduleTripleRightValueIso,
    derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id,
    Iso.app_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc] at h ⊢
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonInner

/-! ## BimoduleCompositionPentagonComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonComparison.lean） -/

/-! # 全導来五角図式の始域と両終域のK-flat比較

## 概要
全導来五角図式の始域と両終域のK-flat比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonShort.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonComparison
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

/-- 短経路の最初の二因子比較と整合する三つの作用関手の比較。 -/
def derivedBimoduleTripleSourceIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj) ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj) ≅
      rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ⋙
        rightKFlatDerivedCompose A B F G S :=
  isoWhiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (isoWhiskerRight (derivedBimoduleComposeKFlatIso A B E F hF R)
        ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≪≫
      isoWhiskerLeft (rightKFlatDerivedCompose A B E F R)
        (derivedBimoduleComposeKFlatIso A B F G hG S)) ≪≫
    isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q)
      (rightKFlatDerivedCompose A B E F R ⋙ rightKFlatDerivedCompose A B F G S)

def derivedBimoduleTripleLeftFunctorIso (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C F G hG).obj
          ((bimoduleToDerived A F G).obj S.obj)).obj
            (((derivedBimoduleComposeFunctor A C E F hF).obj
              ((bimoduleToDerived A E F).obj R.obj)).obj ((bimoduleToDerived A C E).obj Q.obj))) ≅
      rightKFlatDerivedCompose A B C G
        (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S) :=
  (derivedBimoduleComposeFunctor A B C G hG).mapIso
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S) ≪≫
    derivedBimoduleComposeKFlatIso A B C G hG
      (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)

def derivedBimoduleTripleRightFunctorIso (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj
            ((bimoduleToDerived A F G).obj S.obj)).obj ((bimoduleToDerived A E F).obj R.obj))).obj
              ((bimoduleToDerived A C E).obj Q.obj)) ≅
      rightKFlatDerivedCompose A B C G
        (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S)) :=
  (derivedBimoduleComposeFunctor A B C G hG).mapIso
      (derivedBimoduleTripleRightValueIso A C E F G hG Q R S) ≪≫
    derivedBimoduleComposeKFlatIso A B C G hG
      (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))

/-- 内側の全結合射を作用関手へ送った射の比較square。 -/
lemma derivedBimoduleTripleFunctorIso_associator (hF : localHomKFlat A F)
    (hG : localHomKFlat A G) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).map
        ((derivedBimoduleAssociator A C E F G hF hG
          ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
            ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleLeftFunctorIso A B C E F G hF hG Q R S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom := by
  have hv := derivedBimoduleTripleValueIso_associator A C E F G hF hG Q R S
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C G hG
    (show rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S ⟶
      rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S) from
        ⟨(associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom⟩)
  change _ ≫ ((derivedBimoduleComposeFunctor A B C G hG).map
      (derivedBimoduleTripleRightValueIso A C E F G hG Q R S).hom ≫ _) =
    ((derivedBimoduleComposeFunctor A B C G hG).map
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S).hom ≫ _) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hv,
    CategoryTheory.Functor.map_comp, Category.assoc, hk, ← Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonComparison

/-! ## BimoduleCompositionPentagonShort（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonShort.lean） -/

/-! # 全導来五角図式の短経路のK-flat比較

## 概要
全導来五角図式の短経路のK-flat比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonKFlat.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonShort
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

lemma derivedBimodulePentagonShort_middle (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      (derivedBimoduleAssociator A B E F G hF hG
        ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom ≫
      (derivedBimoduleComposePairComparisonIso A B C E G hE hG Q
        (rightKFlatCompose A E F G R S) (Iso.refl _)
        (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom := by
  ext P
  let FQ := (derivedBimoduleComposeFunctor A B C E hE).obj
    ((bimoduleToDerived A C E).obj Q.obj)
  let KQ := rightKFlatDerivedCompose A B C E Q
  let c := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P
  let RS := rightKFlatCompose A E F G R S
  have hx := (derivedBimoduleComposeKFlatIso A B E G hG RS).hom.naturality c
  have hy := (rightKFlatDerivedAssociator A B E F G R S).hom.naturality c
  have ha := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A B E F G hF hG R S) (FQ.obj P)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha
  change (derivedBimoduleAssociator A B E F G hF hG
      ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
        (FQ.obj P) ≫ _ = _ at ha
  simp only [derivedBimoduleComposePairComparisonIso, derivedBimoduleTripleSourceIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id,
    whiskerRight_id', Category.id_comp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  simp only [Category.assoc] at ha ⊢
  rw [hx]
  simp only [← Category.assoc] at ha ⊢
  rw [ha]
  simp only [Category.assoc]
  rw [← hy]

lemma derivedBimodulePentagonShort_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom ≫
      (rightKFlatDerivedAssociator A B C E G Q (rightKFlatCompose A E F G R S)).hom := by
  have h := derivedBimoduleAssociator_comparison_fac A B C E G hE hG Q
    (rightKFlatCompose A E F G R S) (Iso.refl _)
    (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)
  change (derivedBimoduleAssociator A B C E G hE hG _ _).hom ≫
    (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom = _ at h
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc, derivedBimodulePentagonShort_middle, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonShort

/-! ## BimoduleCompositionPentagonKFlat（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonKFlat.lean） -/

/-! # 全導来五角図式の長経路とK-flat三因子の比較

## 概要
全導来五角図式の長経路とK-flat三因子の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionFamilies.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonKFlat
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

def derivedBimoduleTripleSourceAltIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj) ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj) ≅
      rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ⋙
        rightKFlatDerivedCompose A B F G S :=
  isoWhiskerRight
      (isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q)
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj)) ≪≫
        isoWhiskerLeft (rightKFlatDerivedCompose A B C E Q)
          (derivedBimoduleComposeKFlatIso A B E F hF R))
      ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≪≫
    isoWhiskerLeft (rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R)
      (derivedBimoduleComposeKFlatIso A B F G hG S)

lemma derivedBimoduleTripleSourceAltIso_eq (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimoduleTripleSourceAltIso A B C E F G hE hF hG Q R S =
      derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S := by
  apply Iso.ext
  ext P
  have hr := (derivedBimoduleComposeKFlatIso A B E F hF R).hom.naturality
    ((derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P)
  have hm := congrArg
    ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).map hr
  simp only [CategoryTheory.Functor.map_comp] at hm
  have hs := (derivedBimoduleComposeKFlatIso A B F G hG S).hom.naturality
    ((rightKFlatDerivedCompose A B E F R).map
      ((derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P))
  simp only [derivedBimoduleTripleSourceAltIso, derivedBimoduleTripleSourceIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, rightKFlatDerivedCompose] at hm hs ⊢
  rw [reassoc_of% hm, hs]

lemma derivedBimodulePentagonLong_middle (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    whiskerRight (derivedBimoduleAssociator A B C E F hE hF
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)).hom
      ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≫
      (derivedBimoduleComposePairComparisonIso A B C F G hF hG (rightKFlatCompose A C E F Q R)
        S (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) := by
  rw [← derivedBimoduleTripleSourceAltIso_eq]
  ext P
  have ha := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A B C E F hE hF Q R) P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha
  change (derivedBimoduleAssociator A B C E F hE hF _ _).hom.app P ≫ _ = _ at ha
  have hm := congrArg
    ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).map ha
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hm
  have hs := (derivedBimoduleComposeKFlatIso A B F G hG S).hom.naturality
    ((rightKFlatDerivedAssociator A B C E F Q R).hom.app P)
  simp only [derivedBimoduleComposePairComparisonIso, derivedBimoduleTripleSourceAltIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id, whiskerLeft_id',
    Category.id_comp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hm, hs]

lemma derivedBimodulePentagonLong_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) ≫
      (rightKFlatDerivedAssociator A B C F G (rightKFlatCompose A C E F Q R) S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom := by
  have h := derivedBimoduleAssociator_comparison_fac A B C F G hF hG
    (rightKFlatCompose A C E F Q R) S
    (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)
  change (derivedBimoduleAssociator A B C F G hF hG _ _).hom ≫
    (derivedBimoduleTripleLeftFunctorIso A B C E F G hF hG Q R S).hom = _ at h
  change (_ ≫ (_ ≫ _)) ≫ _ = _
  simp only [Category.assoc]
  rw [derivedBimoduleTripleFunctorIso_associator]
  rw [reassoc_of% h]
  rw [← Category.assoc, derivedBimodulePentagonLong_middle, Category.assoc]

lemma derivedBimodulePentagon_kFlat (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) =
      derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) := by
  apply (Iso.cancel_iso_hom_right _ _
    (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S)).1
  rw [derivedBimodulePentagonShort_kFlat_fac, derivedBimodulePentagonLong_kFlat_fac,
    derivedPentagon]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonKFlat

/-! ## BimoduleCompositionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionFamilies.lean） -/

/-! # 任意のパラメータ圏上の導来bimodule合成と結合比較

## 概要
任意のパラメータ圏上の導来bimodule合成と結合比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonFamilies.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionFamilies
universe u v w z t x s s'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable {T : Type s} [Category.{s'} T]

omit [DGCategory A B] [Small.{u} B] [DGCategory A G] [Small.{u} G] in
def derivedBimoduleComposeFamily (hF : localHomKFlat A F)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F) :
    T ⥤ DerivedBimoduleCategory A C F :=
  Q.prod' (R ⋙ derivedBimoduleComposeFunctor A C E F hF) ⋙
    evaluationUncurried (DerivedBimoduleCategory A C E) (DerivedBimoduleCategory A C F)

omit [DGCategory A G] [Small.{u} G] in
def derivedBimoduleAssociatorFamily (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F) :
    compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
        (R ⋙ derivedBimoduleComposeFunctor A B E F hF) ≅
      derivedBimoduleComposeFamily A C E F hF Q R ⋙ derivedBimoduleComposeFunctor A B C F hF :=
  NatIso.ofComponents
    (fun t => derivedBimoduleAssociator A B C E F hE hF (Q.obj t) (R.obj t))
    (fun f => derivedBimoduleAssociator_naturality A B C E F hE hF (Q.map f) (R.map f))

omit [DGCategory A B] [Small.{u} B] in
def derivedBimoduleInnerAssociatorFamily (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F)
    (S : T ⥤ DerivedBimoduleCategory A F G) :
    derivedBimoduleComposeFamily A C F G hG (derivedBimoduleComposeFamily A C E F hF Q R) S ≅
      derivedBimoduleComposeFamily A C E G hG Q (derivedBimoduleComposeFamily A E F G hG R S) :=
  NatIso.ofComponents
    (fun t => (derivedBimoduleAssociator A C E F G hF hG (R.obj t) (S.obj t)).app (Q.obj t))
    (fun {i j} f => by
      have hQ := (derivedBimoduleAssociator A C E F G hF hG (R.obj i) (S.obj i)).hom.naturality
        (Q.map f)
      simp only [Functor.comp_map] at hQ
      have hRS := NatTrans.congr_app
        (derivedBimoduleAssociator_naturality A C E F G hF hG (R.map f) (S.map f)) (Q.obj j)
      simp only [derivedBimoduleComposePairMap, NatTrans.comp_app, whiskerRight_app,
        whiskerLeft_app, Category.assoc] at hRS
      change
        (((derivedBimoduleComposeFunctor A C F G hG).obj (S.obj i)).map
          (((derivedBimoduleComposeFunctor A C E F hF).obj (R.obj i)).map (Q.map f) ≫
            ((derivedBimoduleComposeFunctor A C E F hF).map (R.map f)).app (Q.obj j)) ≫
          ((derivedBimoduleComposeFunctor A C F G hG).map (S.map f)).app
            (((derivedBimoduleComposeFunctor A C E F hF).obj (R.obj j)).obj (Q.obj j))) ≫
          (derivedBimoduleAssociator A C E F G hF hG (R.obj j) (S.obj j)).hom.app (Q.obj j) =
        (derivedBimoduleAssociator A C E F G hF hG (R.obj i) (S.obj i)).hom.app (Q.obj i) ≫
          (((derivedBimoduleComposeFunctor A C E G hG).obj
            (((derivedBimoduleComposeFunctor A E F G hG).obj (S.obj i)).obj (R.obj i))).map
              (Q.map f) ≫
            ((derivedBimoduleComposeFunctor A C E G hG).map
              (derivedBimoduleComposeInnerMap A E F G hG (R.map f) (S.map f))).app (Q.obj j))
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [hRS]
      rw [← Category.assoc, hQ, Category.assoc])

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionFamilies

/-! ## BimoduleCompositionPentagonFamilies（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagonFamilies.lean） -/

/-! # 五角の両経路の任意のパラメータ族に関する自然性

## 概要
五角の両経路の任意のパラメータ族に関する自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagon.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagonFamilies
universe u v w z t x s s'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable {T : Type s} [Category.{s'} T]
variable (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
  (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F)
  (S : T ⥤ DerivedBimoduleCategory A F G)

def derivedBimodulePentagonShortFamily :
    compositionFamily
        (compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
          (R ⋙ derivedBimoduleComposeFunctor A B E F hF))
        (S ⋙ derivedBimoduleComposeFunctor A B F G hG) ⟶
      derivedBimoduleComposeFamily A C E G hG Q
        (derivedBimoduleComposeFamily A E F G hG R S) ⋙
          derivedBimoduleComposeFunctor A B C G hG :=
  (compositionFamilyAssociator (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
      (R ⋙ derivedBimoduleComposeFunctor A B E F hF)
      (S ⋙ derivedBimoduleComposeFunctor A B F G hG)).hom ≫
    compositionFamilyMap (𝟙 (Q ⋙ derivedBimoduleComposeFunctor A B C E hE))
      (derivedBimoduleAssociatorFamily A B E F G hF hG R S).hom ≫
    (derivedBimoduleAssociatorFamily A B C E G hE hG Q
      (derivedBimoduleComposeFamily A E F G hG R S)).hom

def derivedBimodulePentagonLongFamily :
    compositionFamily
        (compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
          (R ⋙ derivedBimoduleComposeFunctor A B E F hF))
        (S ⋙ derivedBimoduleComposeFunctor A B F G hG) ⟶
      derivedBimoduleComposeFamily A C E G hG Q
        (derivedBimoduleComposeFamily A E F G hG R S) ⋙
          derivedBimoduleComposeFunctor A B C G hG :=
  compositionFamilyMap (derivedBimoduleAssociatorFamily A B C E F hE hF Q R).hom
      (𝟙 (S ⋙ derivedBimoduleComposeFunctor A B F G hG)) ≫
    (derivedBimoduleAssociatorFamily A B C F G hF hG
      (derivedBimoduleComposeFamily A C E F hF Q R) S).hom ≫
    whiskerRight (derivedBimoduleInnerAssociatorFamily A C E F G hF hG Q R S).hom
      (derivedBimoduleComposeFunctor A B C G hG)

lemma derivedBimodulePentagonShortFamily_app (i : T) :
    (derivedBimodulePentagonShortFamily A B C E F G hE hF hG Q R S).app i =
      derivedBimodulePentagonShort A B C E F G hE hF hG (Q.obj i) (R.obj i) (S.obj i) := by
  ext P
  dsimp [derivedBimodulePentagonShortFamily, compositionFamilyMap, compositionFamilyAssociator,
    compositionFamily, derivedBimoduleComposeFamily, derivedBimoduleAssociatorFamily,
    derivedBimodulePentagonShort, uncurry, whiskeringLeft]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

lemma derivedBimodulePentagonLongFamily_app (i : T) :
    (derivedBimodulePentagonLongFamily A B C E F G hE hF hG Q R S).app i =
      derivedBimodulePentagonLong A B C E F G hE hF hG (Q.obj i) (R.obj i) (S.obj i) := by
  ext P
  dsimp [derivedBimodulePentagonLongFamily, compositionFamilyMap, derivedBimoduleComposeFamily,
    derivedBimoduleAssociatorFamily, derivedBimoduleInnerAssociatorFamily,
    derivedBimodulePentagonLong, uncurry, whiskeringLeft]
  simp only [Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagonFamilies

/-! ## BimoduleCompositionPentagon（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPentagon.lean） -/

/-! # 全導来bimodule因子上の五角恒等式

## 概要
全導来bimodule因子上の五角恒等式。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleLocal.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPentagon
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

omit [DGCategory A B] [DGCategory A F] [DGCategory A G]
    [Small.{u} B] [Small.{u} F] [Small.{u} G] in
lemma exists_rightKFlat_derived_iso (hE : localHomKFlat A E)
    (M : DerivedBimoduleCategory A C E) :
    ∃ P : RightKFlatBimoduleCategory A C E,
      Nonempty ((bimoduleToDerived A C E).obj P.obj ≅ M) := by
  let J := rightKFlatDerivedInclusion A C E
  let L := rightKFlatToDerived A C E
  let : J.EssSurj := rightKFlatDerivedInclusion_essSurj A C E hE
  let X := J.objPreimage M
  let P := L.objPreimage X
  refine ⟨P, ⟨?_⟩⟩
  exact J.mapIso (L.objObjPreimageIso X) ≪≫ J.objObjPreimageIso M

/-- 全三つの導来後因子について五角の二経路が一致する。前因子にも自然。 -/
lemma derivedBimodulePentagon (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : DerivedBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG Q R S =
      derivedBimodulePentagonLong A B C E F G hE hF hG Q R S := by
  let T := DerivedBimoduleCategory A C E ×
    (DerivedBimoduleCategory A E F × DerivedBimoduleCategory A F G)
  let q : T ⥤ DerivedBimoduleCategory A C E := CategoryTheory.Prod.fst _ _
  let r : T ⥤ DerivedBimoduleCategory A E F :=
    CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _
  let s : T ⥤ DerivedBimoduleCategory A F G :=
    CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _
  let U := compositionFamily
    (compositionFamily (q ⋙ derivedBimoduleComposeFunctor A B C E hE)
      (r ⋙ derivedBimoduleComposeFunctor A B E F hF))
    (s ⋙ derivedBimoduleComposeFunctor A B F G hG)
  let a := derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s
  let b := derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s
  obtain ⟨Q₀, ⟨eQ⟩⟩ := exists_rightKFlat_derived_iso A C E hE Q
  obtain ⟨R₀, ⟨eR⟩⟩ := exists_rightKFlat_derived_iso A E F hF R
  obtain ⟨S₀, ⟨eS⟩⟩ := exists_rightKFlat_derived_iso A F G hG S
  let V : T := ((bimoduleToDerived A C E).obj Q₀.obj,
    ((bimoduleToDerived A E F).obj R₀.obj, (bimoduleToDerived A F G).obj S₀.obj))
  let e : V ≅ (Q, (R, S)) := eQ.prod (eR.prod eS)
  have hV : a.app V = b.app V := by
    change (derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s).app V =
      (derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s).app V
    rw [derivedBimodulePentagonShortFamily_app, derivedBimodulePentagonLongFamily_app]
    exact derivedBimodulePentagon_kFlat A B C E F G hE hF hG Q₀ R₀ S₀
  have h : a.app (Q, (R, S)) = b.app (Q, (R, S)) := by
    apply (Iso.cancel_iso_hom_left (U.mapIso e) _ _).1
    change U.map e.hom ≫ _ = U.map e.hom ≫ _
    rw [a.naturality, b.naturality, hV]
  change (derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s).app (Q, (R, S)) =
    (derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s).app (Q, (R, S)) at h
  rw [derivedBimodulePentagonShortFamily_app, derivedBimodulePentagonLongFamily_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPentagon
