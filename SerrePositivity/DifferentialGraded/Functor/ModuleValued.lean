module

public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Adjunction.Basic
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
# Functor.ModuleValued

## 概要
7 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## HomotopyAdjunction（旧 SerrePositivity/DifferentialGraded/Functor/HomotopyAdjunction.lean） -/

/-! # dg関手の閉零随伴の主ホモトピー圏への降下

## 概要
dg関手の閉零随伴の主ホモトピー圏への降下。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section HomotopyAdjunction
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]
  (L : DGFunctor A D E) (R : DGFunctor A E D) (adj : L.onClosed ⊣ R.onClosed)

/-- 閉零随伴の単位を境界商へ送る。 -/
def homotopyAdjunctionUnit : 𝟭 (HomotopyCategory A D) ⟶ L.onHomotopy ⋙ R.onHomotopy where
  app X := (toHomotopy A D).map (adj.unit.app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    change (toHomotopy A D).map f ≫ (toHomotopy A D).map (adj.unit.app Y) =
      (toHomotopy A D).map (adj.unit.app X) ≫
        (toHomotopy A D).map (R.onClosed.map (L.onClosed.map f))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (toHomotopy A D).map (adj.unit.naturality f)

/-- 閉零随伴の余単位を境界商へ送る。 -/
def homotopyAdjunctionCounit : R.onHomotopy ⋙ L.onHomotopy ⟶ 𝟭 (HomotopyCategory A E) where
  app X := (toHomotopy A E).map (adj.counit.app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (toHomotopy A E).map_surjective f
    change (toHomotopy A E).map (L.onClosed.map (R.onClosed.map f)) ≫
      (toHomotopy A E).map (adj.counit.app Y) =
        (toHomotopy A E).map (adj.counit.app X) ≫ (toHomotopy A E).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (toHomotopy A E).map (adj.counit.naturality f)

lemma homotopyAdjunction_left_triangle (X : HomotopyCategory A D) :
    L.onHomotopy.map ((homotopyAdjunctionUnit L R adj).app X) ≫
      (homotopyAdjunctionCounit L R adj).app (L.onHomotopy.obj X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (toHomotopy A E).map (L.onClosed.map (adj.unit.app X)) ≫
    (toHomotopy A E).map (adj.counit.app (L.onClosed.obj X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg (toHomotopy A E).map (adj.left_triangle_components X)).trans
    ((toHomotopy A E).map_id _)

lemma homotopyAdjunction_right_triangle (X : HomotopyCategory A E) :
    (homotopyAdjunctionUnit L R adj).app (R.onHomotopy.obj X) ≫
      R.onHomotopy.map ((homotopyAdjunctionCounit L R adj).app X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (toHomotopy A D).map (adj.unit.app (R.onClosed.obj X)) ≫
    (toHomotopy A D).map (R.onClosed.map (adj.counit.app X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg (toHomotopy A D).map (adj.right_triangle_components X)).trans
    ((toHomotopy A D).map_id _)

/-- 二つのdg関手の閉零随伴は主ホモトピー圏の随伴を誘導する。 -/
def homotopyAdjunction : L.onHomotopy ⊣ R.onHomotopy :=
  Adjunction.mkOfUnitCounit {
    unit := homotopyAdjunctionUnit L R adj
    counit := homotopyAdjunctionCounit L R adj
    left_triangle := by
      apply NatTrans.ext
      funext X
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using
          homotopyAdjunction_left_triangle L R adj X
    right_triangle := by
      apply NatTrans.ext
      funext X
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using
          homotopyAdjunction_right_triangle L R adj X }

/-- 商へ送った実際の射について随伴Hom同値も商への関手と可換。 -/
lemma homotopyAdjunction_homEquiv_map (X : ClosedCategory A D) (Y : ClosedCategory A E)
    (f : L.onClosed.obj X ⟶ Y) :
    (homotopyAdjunction L R adj).homEquiv ((toHomotopy A D).obj X)
        ((toHomotopy A E).obj Y) ((toHomotopy A E).map f) =
      (toHomotopy A D).map (adj.homEquiv X Y f) := by
  rw [Adjunction.homEquiv_unit]
  change (toHomotopy A D).map (adj.unit.app X) ≫
    (toHomotopy A D).map (R.onClosed.map f) = _
  rw [← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.DGFunctor
end

end HomotopyAdjunction

/-! ## ContractingElements（旧 SerrePositivity/DifferentialGraded/Functor/ContractingElements.lean） -/

/-! # dg関手による微分と指定収縮元の保存 -/

@[expose] public section ContractingElements
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

lemma map_differential_element (F : DGFunctor A D E) {x y : D} (n : ℤ)
    (f : GradedHom A x y n) :
    (F.map x y).f (n + 1) (differential A f) =
      differential A ((F.map x y).f n f) := by
  exact (ConcreteCategory.congr_hom ((F.map x y).comm n (n + 1)) f).symm

lemma map_contractingElement (F : DGFunctor A D E) (x : D)
    (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    (homObject A E (F.obj x) (F.obj x)).d (-1) 0 ((F.map x x).f (-1) h) =
      (unitElement A (F.obj x)).val := by
  have hc := ConcreteCategory.congr_hom ((F.map x x).comm (-1) 0) h
  change (homObject A E (F.obj x) (F.obj x)).d (-1) 0 ((F.map x x).f (-1) h) =
    (F.map x x).f 0 ((homObject A D x x).d (-1) 0 h) at hc
  rw [dh, map_unitElement] at hc
  exact hc

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ContractingElements

/-! ## HomogeneousNaturality（旧 SerrePositivity/DifferentialGraded/Functor/HomogeneousNaturality.lean） -/

/-!
概要：任意次数の変換成分の自然性を、斉次射ごとの条件として扱う。
方針：Koszul 符号を明示し、合成に関する閉性を豊穣結合則から導く。
規約：次数零や閉射だけへ制限しない。
使われ方：D-8 e の同じ実商の元 Hom・ε から全 path への全次数自然性。
-/

@[expose] public section HomogeneousNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {E : Type w} [DGCategory R E]

lemma forward_units_smul_first {x y z : E} {p q n : ℤ}
    (s : ℤˣ) (f : GradedHom R x y p) (g : GradedHom R y z q) (hn : p + q = n) :
    forward R (s • f) g hn = s • forward R f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_zsmul]

lemma forward_units_smul_second {x y z : E} {p q n : ℤ}
    (s : ℤˣ) (f : GradedHom R x y p) (g : GradedHom R y z q) (hn : p + q = n) :
    forward R f (s • g) hn = s • forward R f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

/-- 全次数の元の射 f に対する、次数 k の変換成分の自然性。 -/
def homogeneousNaturalityAt (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    {x y : D} {p : ℤ} (f : GradedHom R x y p) : Prop :=
  forward R ((F.map x y).f p f) (a y) rfl =
    (k * p).negOnePow • forward R (a x) ((G.map x y).f p f) (by omega)

lemma homogeneousNaturalityAt_forward (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    {x y z : D} {p q : ℤ} (f : GradedHom R x y p) (g : GradedHom R y z q)
    (hf : homogeneousNaturalityAt R F G a f) (hg : homogeneousNaturalityAt R F G a g) :
    homogeneousNaturalityAt R F G a (forward R f g rfl) := by
  dsimp only [homogeneousNaturalityAt] at hf hg ⊢
  rw [DGFunctor.map_forward, DGFunctor.map_forward]
  rw [forward_assoc_of_sum R _ _ _ rfl rfl rfl, hg, forward_units_smul_second]
  rw [← forward_assoc_of_sum R _ _ _ rfl (by omega) (by omega), hf,
    forward_units_smul_first, forward_assoc_of_sum R _ _ _ (by omega) rfl (by omega)]
  rw [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

def homogeneousNaturalityLeftCochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    Cochain (homObject R D x y) (homObject R E (F.obj x) (G.obj y)) k :=
  Cochain.mk (fun i j hij => (F.map x y).f i ≫
    ModuleCat.ofHom ((TensorProduct.mk R _ _).flip (a y)) ≫
    ιTensorObj (homObject R E (F.obj x) (F.obj y))
      (homObject R E (F.obj y) (G.obj y)) i k j hij ≫
    (eComp (Complex R) (F.obj x) (F.obj y) (G.obj y)).f j)

def homogeneousNaturalityRightCochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    Cochain (homObject R D x y) (homObject R E (F.obj x) (G.obj y)) k :=
  Cochain.mk (fun i j hij => (k * i).negOnePow • ((G.map x y).f i ≫
    ModuleCat.ofHom (TensorProduct.mk R _ _ (a x)) ≫
    ιTensorObj (homObject R E (F.obj x) (G.obj x))
      (homObject R E (G.obj x) (G.obj y)) k i j (by omega) ≫
    (eComp (Complex R) (F.obj x) (G.obj x) (G.obj y)).f j))

lemma homogeneousNaturalityAt_iff_cochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    (∀ (p : ℤ) (f : GradedHom R x y p), homogeneousNaturalityAt R F G a f) ↔
      homogeneousNaturalityLeftCochain R F G a x y =
        homogeneousNaturalityRightCochain R F G a x y := by
  constructor
  · intro h
    apply Cochain.ext
    intro i j hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact h i f
  · intro h p f
    exact congrArg (fun z => z f) (Cochain.congr_v h p (p + k) rfl)

lemma gradedFamilyNaturality_iff_homogeneous (F G : DGFunctor R D E) {K : Complex R}
    (a : ∀ x, K ⟶ homObject R E (F.obj x) (G.obj x)) (x y : D) :
    ((β_ K (homObject R D x y)).hom ≫ (F.map x y ⊗ₘ a y) ≫
        eComp (Complex R) _ _ _ = (a x ⊗ₘ G.map x y) ≫ eComp (Complex R) _ _ _) ↔
      ∀ (k p : ℤ) (t : K.X k) (f : GradedHom R x y p),
        homogeneousNaturalityAt R F G (fun z => (a z).f k t) f := by
  constructor
  · intro h k p t f
    have ht := congrArg (fun m => m.f (p + k)
      (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f))) h
    change (eComp (Complex R) _ _ _).f (p + k)
      ((F.map x y ⊗ₘ a y).f (p + k)
        ((signedSwap K (homObject R D x y)).hom.f (p + k)
          (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f)))) =
      (eComp (Complex R) _ _ _).f (p + k) ((a x ⊗ₘ G.map x y).f (p + k)
        (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f))) at ht
    rw [signedSwap_apply] at ht
    simp only [Units.smul_def, map_zsmul] at ht
    rw [tensorMap_apply, tensorMap_apply] at ht
    have h' : (k * p).negOnePow • forward R ((F.map x y).f p f) ((a y).f k t) rfl =
        forward R ((a x).f k t) ((G.map x y).f p f) (by omega) := ht
    have hs := congrArg (fun z => (k * p).negOnePow • z) h'
    rw [smul_smul, Int.units_mul_self, one_smul] at hs
    exact hs
  · intro h
    apply tensorHom_ext
    intro k p n hkn
    have hpn : p + k = n := by omega
    cases hpn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro t f
    change (eComp (Complex R) _ _ _).f (p + k)
      ((F.map x y ⊗ₘ a y).f (p + k)
        ((signedSwap K (homObject R D x y)).hom.f (p + k)
          (ιTensorObj K (homObject R D x y) k p (p + k) hkn (t ⊗ₜ[R] f)))) =
      (eComp (Complex R) _ _ _).f (p + k) ((a x ⊗ₘ G.map x y).f (p + k)
        (ιTensorObj K (homObject R D x y) k p (p + k) hkn (t ⊗ₜ[R] f)))
    rw [signedSwap_apply]
    simp only [Units.smul_def, map_zsmul]
    rw [tensorMap_apply, tensorMap_apply]
    have ht := h k p t f
    change forward R ((F.map x y).f p f) ((a y).f k t) rfl =
      (k * p).negOnePow • forward R ((a x).f k t) ((G.map x y).f p f) (by omega) at ht
    change (k * p).negOnePow • forward R ((F.map x y).f p f) ((a y).f k t) rfl = _
    rw [ht, smul_smul, Int.units_mul_self, one_smul]
    rfl

end SerrePositivity.DifferentialGraded
end

end HomogeneousNaturality

/-! ## CoproductMatrixComparison（旧 SerrePositivity/DifferentialGraded/Functor/CoproductMatrixComparison.lean） -/

/-!
概要：直和を保つ加法的閉関手について、行有限行列の端点同型付き可換性を束ねる。
方針：余積包含で射を検出し、各行の有限和と元の端点比較を照合する。
規約：行列全体の実射の等式を得る。
使われ方：c′ の自由 sphere 行列の実延長比較を全直和へ接続する。
-/

@[expose] public section CoproductMatrixComparison
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable {C : Type v} {E : Type w} [Category C] [Category E]

def coproductFamilyImageIso {I : Type u} [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    (F : C ⥤ E) (A : I → C) (B : I → E)
    [PreservesColimit (Discrete.functor A) F] (e : ∀ i, F.obj (A i) ≅ B i) :
    F.obj (∐ A) ≅ ∐ B :=
  PreservesCoproduct.iso F A ≪≫ Sigma.mapIso e

lemma coproductFamilyImageIso_ι {I : Type u}
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    (F : C ⥤ E) (A : I → C) (B : I → E)
    [PreservesColimit (Discrete.functor A) F] (e : ∀ i, F.obj (A i) ≅ B i) (i : I) :
    F.map (Sigma.ι A i) ≫ (coproductFamilyImageIso F A B e).hom =
      (e i).hom ≫ Sigma.ι B i := by
  have h := (isColimitOfHasCoproductOfPreservesColimit F A).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun i => F.obj (A i))) ⟨i⟩
  change F.map (Sigma.ι A i) ≫ (PreservesCoproduct.iso F A).hom = _ at h
  simp only [coproductFamilyImageIso, Iso.trans_hom, ← Category.assoc]
  rw [h]
  change Sigma.ι (fun i => F.obj (A i)) i ≫ (Sigma.mapIso e).hom = _
  exact Sigma.ι_mapIso_hom e i

lemma coproductFamilyImageIso_matrix [Preadditive C] [Preadditive E]
    {I J : Type u} [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    [HasCoproductsOfShape J C] [HasCoproductsOfShape J E]
    (F : C ⥤ E) [F.Additive] (A : I → C) (B : J → C) (A' : I → E) (B' : J → E)
    [PreservesColimit (Discrete.functor A) F] [PreservesColimit (Discrete.functor B) F]
    (a : ∀ i, F.obj (A i) ≅ A' i) (b : ∀ j, F.obj (B j) ≅ B' j)
    (s : I → Finset J) (g : ∀ i j, A i ⟶ B j) (f : ∀ i j, A' i ⟶ B' j)
    (h : ∀ i j, j ∈ s i → F.map (g i j) ≫ (b j).hom = (a i).hom ≫ f i j) :
    F.map (Sigma.desc (fun i => ∑ j ∈ s i, g i j ≫ Sigma.ι B j)) ≫
      (coproductFamilyImageIso F B B' b).hom =
    (coproductFamilyImageIso F A A' a).hom ≫
      Sigma.desc (fun i => ∑ j ∈ s i, f i j ≫ Sigma.ι B' j) := by
  classical
  apply (isColimitOfHasCoproductOfPreservesColimit F A).hom_ext
  rintro ⟨i⟩
  change F.map (Sigma.ι A i) ≫ _ = F.map (Sigma.ι A i) ≫ _
  rw [← F.map_comp_assoc, Sigma.ι_desc]
  rw [← Category.assoc, coproductFamilyImageIso_ι, Category.assoc, Sigma.ι_desc]
  simp only [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum,
    F.map_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coproductFamilyImageIso_ι, ← Category.assoc, h i j hj]
  simp only [Category.assoc]

end SerrePositivity.DifferentialGraded
end

end CoproductMatrixComparison

/-! ## ModuleValuedCone（旧 SerrePositivity/DifferentialGraded/Functor/ModuleValuedCone.lean） -/

/-!
概要：加群値 dg 関手と標準 cone の実比較射を構成する。
方針：既存の Endomorphism.ModuleConeImage の同じ実比較を公開入口で再利用する。
規約：全加群型の Small 性を仮定せず、全 Hom 複体への dg 作用を使う。
使われ方：ラベル付き提示模型の cone 演算と、実 dg 加群延長の比較。
-/

@[expose] public section ModuleValuedCone
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))
  {M N : ModuleCategory A D} (f : M ⟶ N)

def moduleValuedConeInl :
    GradedHom A (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f))) (-1) :=
  dgModuleFunctorConeInl A D E F f

lemma moduleValuedConeInl_d :
    (homObject A (RightModule A E) (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (moduleValuedConeInl A D E F f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (F.onClosed.map f ≫ F.onClosed.map (moduleConeInr A D f)))).val :=
  dgModuleFunctorConeInl_d A D E F f

def moduleValuedConeComparison :
    moduleCone A E (F.onClosed.map f) ⟶ F.onClosed.obj (moduleCone A D f) :=
  dgModuleFunctorConeComparison A D E F f

lemma moduleValuedConeComparison_eval (x : E) :
    (moduleEvaluation A E x).map (moduleValuedConeComparison A D E F f) =
      moduleConeImageComparison A D (F.comp (moduleEvaluationDG A E x)) f :=
  dgModuleFunctorConeComparison_eval A D E F f x

instance moduleValuedConeComparison_isIso :
    IsIso (moduleValuedConeComparison A D E F f) :=
  dgModuleFunctorConeComparison_isIso A D E F f

/-- 加群値 dg 関手は、同じ実 cone と全評価の標準比較によって可換する。 -/
def moduleValuedConeIso :
    moduleCone A E (F.onClosed.map f) ≅ F.onClosed.obj (moduleCone A D f) :=
  dgModuleFunctorConeIso A D E F f

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleValuedCone

/-! ## ModuleValuedConeTransport（旧 SerrePositivity/DifferentialGraded/Functor/ModuleValuedConeTransport.lean） -/

/-!
概要：加群値 dg 関手の cone 比較を、指定した両端の実閉同型に沿って輸送する。
方針：元の cone 比較と arrow 圏からの厳密 cone 関手を合成する。
規約：両端同型と元の閉射を保持する。導来圏での同型に置き換えない。
使われ方：ラベル付き cone の評価比較を巨大な具体的延長式から切り離す。
-/

@[expose] public section ModuleValuedConeTransport
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))
  {M N : ModuleCategory A D} (f : M ⟶ N)
  {M' N' : ModuleCategory A E} (a : F.onClosed.obj M ≅ M') (b : F.onClosed.obj N ≅ N')

def moduleValuedConeTransportIso :=
  (moduleValuedConeIso A D E F f).symm ≪≫
    moduleConeIsoOfSquare A E (F.onClosed.map f) (a.inv ≫ F.onClosed.map f ≫ b.hom)
      a b (by simp)

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleValuedConeTransport
