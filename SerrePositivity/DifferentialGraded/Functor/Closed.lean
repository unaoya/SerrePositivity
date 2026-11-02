module

public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugationLaws
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Functor.DGClosedComparisonIso
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGParameterConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition

/-!
# Functor.Closed

## 概要
10 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Tensor（旧 SerrePositivity/DifferentialGraded/Functor/Tensor.lean） -/

/-! # 二つのdg関手のtensor積

## 概要
Hom chain mapのtensor積と、Mathlib tensorμの自然性を使う。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Tensor
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w} {D : Type z} {E : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]

def tensor (F : DGFunctor A B D) (G : DGFunctor A C E) :
    DGFunctor A (DGTensorCategory A B C) (DGTensorCategory A D E) where
  obj x := (F.obj x.1, G.obj x.2)
  map x y := F.map x.1 y.1 ⊗ₘ G.map x.2 y.2
  map_id x := by
    rw [dgTensor_identity, dgTensor_identity, Category.assoc,
      tensorHom_comp_tensorHom, F.map_id, G.map_id]
  map_comp x y z := by
    rw [dgTensor_composition, dgTensor_composition, Category.assoc,
      tensorHom_comp_tensorHom, F.map_comp, G.map_comp,
      ← tensorHom_comp_tensorHom, ← Category.assoc, ← tensorμ_natural, Category.assoc]

end SerrePositivity.DifferentialGraded.DGFunctor
end

end Tensor

/-! ## Opposite（旧 SerrePositivity/DifferentialGraded/Functor/Opposite.lean） -/

/-! # dg関手のopposite -/

@[expose] public section Opposite
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory BraidedCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {F : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A F]

/-- Hom chain mapを保ち、両側のKoszul交換をbraidingの自然性で比較する。 -/
def op (G : DGFunctor A D E) : DGFunctor A Dᵒᵖ Eᵒᵖ where
  obj x := Opposite.op (G.obj x.unop)
  map x y := G.map y.unop x.unop
  map_id x := G.map_id x.unop
  map_comp x y z := by
    change (β_ _ _).hom ≫ eComp (Complex A) z.unop y.unop x.unop ≫
      G.map z.unop x.unop = _
    rw [G.map_comp]
    change (β_ _ _).hom ≫ (G.map z.unop y.unop ⊗ₘ G.map y.unop x.unop) ≫
      eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop) =
      (G.map y.unop x.unop ⊗ₘ G.map z.unop y.unop) ≫ (β_ _ _).hom ≫
        eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop)
    exact (braiding_naturality_assoc (G.map y.unop x.unop) (G.map z.unop y.unop)
      (eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop))).symm

@[simp]
lemma op_id : (DGFunctor.id (A := A) D).op = DGFunctor.id (A := A) Dᵒᵖ := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (DGFunctor.id (A := A) D).op) (G := DGFunctor.id (A := A) Dᵒᵖ) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

@[simp]
lemma op_comp (G : DGFunctor A D E) (H : DGFunctor A E F) :
    (G.comp H).op = G.op.comp H.op := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (G.comp H).op) (G := G.op.comp H.op) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.DGFunctor
end

end Opposite

/-! ## QuasiEquivalenceOpposite（旧 SerrePositivity/DifferentialGraded/Functor/QuasiEquivalenceOpposite.lean） -/

/-! # dg関手のoppositeによる準同値の保存

## 概要
dg関手のoppositeによる準同値の保存。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section QuasiEquivalenceOpposite
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] (F : DGFunctor A D E)

lemma homQuasiIso_op (hF : HomQuasiIso F) : HomQuasiIso F.op :=
  fun x y => hF y.unop x.unop

lemma DGFunctor.onHomotopy_op_essSurj (hF : F.onHomotopy.EssSurj) : F.op.onHomotopy.EssSurj where
  mem_essImage y := by
    let := hF
    let e := ForgetEnrichment.to (Complex A) y.as
    let Y := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e.unop)
    let X := F.onHomotopy.objPreimage Y
    let d := ForgetEnrichment.to (Complex A) X.as
    let i := F.onHomotopy.objObjPreimageIso Y
    refine ⟨(toHomotopy A Dᵒᵖ).obj (ForgetEnrichment.of (Complex A) (Opposite.op d)), ⟨?_⟩⟩
    exact (homotopyOppositeFunctor A E).mapIso i.symm.op

lemma quasiEquivalence_op (hF : QuasiEquivalence F) : QuasiEquivalence F.op :=
  ⟨homQuasiIso_op F hF.1, F.onHomotopy_op_essSurj hF.2⟩

end SerrePositivity.DifferentialGraded
end

end QuasiEquivalenceOpposite

/-! ## ClosedComplex（旧 SerrePositivity/DifferentialGraded/Functor/ClosedComplex.lean） -/

/-! # 複体に値を持つdg関手の閉零・微分・通常順合成 -/

@[expose] public section ClosedComplex
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

def toComplexFunctor (F : DGFunctor A D (Complex A)) : ClosedCategory A D ⥤ Complex A :=
  F.onClosed ⋙ closedToComplex A

lemma map_closedElement (F : DGFunctor A D (Complex A))
    {M N : ClosedCategory A D} (f : M ⟶ N) :
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom ((F.toComplexFunctor A).map f) := by
  have h := mapFromUnit_cochain A
    (F.obj (ForgetEnrichment.to (Complex A) M)) (F.obj (ForgetEnrichment.to (Complex A) N))
    (ForgetEnrichment.homTo (Complex A) f ≫
      F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
  rw [cycleFromUnit_postcomp] at h
  exact h.symm

lemma map_d_cochain (F : DGFunctor A D (Complex A)) {x y : D} {p q : ℤ}
    (z : GradedHom A x y p) :
    (F.map x y).f q ((x ⟶[Complex A] y).d p q z) =
      δ p q ((F.map x y).f p z) := by
  exact (congrArg (fun f => f z) ((F.map x y).comm p q)).symm

lemma map_compose_cochain (F : DGFunctor A D (Complex A)) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (compose A g f hn) =
      ((F.map x y).f p f).comp ((F.map y z).f q g) hn := by
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  rw [map_forward_cochain]
  simp only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ClosedComplex

/-! ## ClosedConjugationPasting（旧 SerrePositivity/DifferentialGraded/Functor/ClosedConjugationPasting.lean） -/

/-!
概要：全 Hom 作用と三つの閉同型による共役を、指定した比較の貼り合わせで整理する。
方針：dg 関手と共役の交換、同型の連結、比較の全 Hom 自然性を順に適用する。
規約：任意の複体パラメータからの chain map を扱い、特定のラベル型に依存しない。
使われ方：表示模型の厳密合成則で、元の三重比較を全 Hom の等号へ送る。
-/

@[expose] public section ClosedConjugationPasting
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] (G : DGFunctor A C D)
  {X X' Y Y' : ClosedCategory A C} {BX BY HX HY TX TY : ClosedCategory A D}
  {K : Complex A}

lemma dgFunctor_conjugation_pasting (a : K ⟶ (X ⟶[Complex A] Y))
    (eX : X ≅ X') (eY : Y ≅ Y')
    (bX : G.onClosed.obj X' ≅ BX) (bY : G.onClosed.obj Y' ≅ BY)
    (tX : BX ≅ TX) (tY : BY ≅ TY)
    (qX : G.onClosed.obj X ≅ HX) (qY : G.onClosed.obj Y ≅ HY)
    (cX : HX ≅ TX) (cY : HY ≅ TY) (h : K ⟶ (HX ⟶[Complex A] HY))
    (hX : G.onClosed.mapIso eX ≪≫ bX ≪≫ tX = qX ≪≫ cX)
    (hY : G.onClosed.mapIso eY ≪≫ bY ≪≫ tY = qY ≪≫ cY)
    (hn : a ≫ G.map (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y) ≫
        enrichedClosedIsoConjugation (Complex A) qX qY = h) :
    a ≫ enrichedClosedIsoConjugation (Complex A) eX eY ≫
      G.map (ForgetEnrichment.to (Complex A) X') (ForgetEnrichment.to (Complex A) Y') ≫
      enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY =
    h ≫ enrichedClosedIsoConjugation (Complex A) cX cY := by
  have he := congrArg (fun k => a ≫ k ≫
    enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY)
    (dgFunctorHom_conjugation A G eX eY)
  simp only [Category.assoc] at he
  rw [he, enrichedClosedIsoConjugation_trans, enrichedClosedIsoConjugation_trans,
    hX, hY, ← enrichedClosedIsoConjugation_trans]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ enrichedClosedIsoConjugation (Complex A) cX cY) hn

end SerrePositivity.DifferentialGraded
end

end ClosedConjugationPasting

/-! ## ClosedConjugationTensorComposition（旧 SerrePositivity/DifferentialGraded/Functor/ClosedConjugationTensorComposition.lean） -/

/-!
概要：全次数の二項合成を保存する鎖写像族は、閉同型で共役した後も合成を保つ。
方針：抽象対象の上で tensor 合成と共役の交換則を一度適用する。
規約：ラベル族の評価や実加群延長を展開しない。
使われ方：大きい提示式の kernel 検査を避ける、豊穣作用の合成法則。
-/

@[expose] public section ClosedConjugationTensorComposition
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] {C : Type v}
  [Category C] [EnrichedOrdinaryCategory (Complex R) C]

lemma enrichedClosedIsoConjugation_preserves_tensor_composition
    {X Y Z X' Y' Z' : C} (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
    {K L M : Complex R} (c : K ⊗ L ⟶ M)
    (a : K ⟶ X ⟶[Complex R] Y) (b : L ⟶ Y ⟶[Complex R] Z)
    (h : M ⟶ X ⟶[Complex R] Z)
    (hc : c ≫ h = (a ⊗ₘ b) ≫ eComp (Complex R) X Y Z) :
    c ≫ (h ≫ enrichedClosedIsoConjugation (Complex R) eX eZ) =
      ((a ≫ enrichedClosedIsoConjugation (Complex R) eX eY) ⊗ₘ
        (b ≫ enrichedClosedIsoConjugation (Complex R) eY eZ)) ≫
          eComp (Complex R) X' Y' Z' := by
  rw [← Category.assoc, hc, Category.assoc,
    ← enrichedClosedIsoConjugation_comp, tensorHom_comp_tensorHom_assoc]

end SerrePositivity.DifferentialGraded
end

end ClosedConjugationTensorComposition

/-! ## ModuleCone（旧 SerrePositivity/DifferentialGraded/Functor/ModuleCone.lean） -/

/-! # dg加群の標準coneと複体値dg関手の比較射 -/

@[expose] public section ModuleCone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- coneの次数−1包含を主dg関手で送ったcochain。 -/
def moduleConeImageInl (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj M) ((F.toComplexFunctor A).obj (moduleCone A D f)) (-1) :=
  (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1) (moduleConeInlElement A D f)

lemma moduleConeImageInl_d (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    δ (-1) 0 (moduleConeImageInl A D F f) =
      Cochain.ofHom ((F.toComplexFunctor A).map f ≫
        (F.toComplexFunctor A).map (moduleConeInr A D f)) := by
  have hd := map_d_cochain A F (q := 0) (moduleConeInlElement A D f)
  have he := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0 z)
    (moduleConeInlElement_d A D f)
  have hc := map_closedElement A F (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at hc
  exact hd.symm.trans (he.trans hc)

/-- 既存の複体coneからdg加群coneの像への標準比較射。 -/
def moduleConeImageComparison (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((F.toComplexFunctor A).map f) ⟶ (F.toComplexFunctor A).obj (moduleCone A D f) :=
  mappingCone.desc ((F.toComplexFunctor A).map f) (moduleConeImageInl A D F f)
    ((F.toComplexFunctor A).map (moduleConeInr A D f)) (moduleConeImageInl_d A D F f)

@[reassoc]
lemma moduleConeImageComparison_inr (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr ((F.toComplexFunctor A).map f) ≫ moduleConeImageComparison A D F f =
      (F.toComplexFunctor A).map (moduleConeInr A D f) :=
  mappingCone.inr_desc _ _ _ _

lemma moduleConeImageComparison_inl (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (mappingCone.inl ((F.toComplexFunctor A).map f)).comp
      (Cochain.ofHom (moduleConeImageComparison A D F f)) (add_zero (-1)) =
      moduleConeImageInl A D F f :=
  mappingCone.inl_desc _ _ _ _

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleCone

/-! ## InducedClosedConjugate（旧 SerrePositivity/DifferentialGraded/Functor/InducedClosedConjugate.lean） -/

/-!
概要：任意のラベル族の間で、実 dg 関手を全次数の閉同型に沿って移す。
方針：ラベルの評価後の関手を既存の全 Hom 共役入口に渡し、標的のラベルを保持する。
規約：KST の4本の一般入口は指示された暫定依存。固有の Perf 宣言を使用しない。
使われ方：小さい提示模型の自由基底・cone・反復段階の共通 dg 作用。
-/

@[expose] public section InducedClosedConjugate
universe u v w i j

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] {I : Type i} {J : Type j}
  (source : I → C) (target : J → D) (F : DGFunctor A C D)
  (obj : I → J)
  (e : ∀ x, ForgetEnrichment.of (Complex A) (F.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (obj x)))

/-- 評価先の選び直しを行わず、全 Hom の共役をラベル間の dg 作用へ持ち上げる。 -/
def inducedDGFunctorClosedConjugate :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    DGFunctor A I J := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  let L := dgFunctorClosedConjugate A ((inducedDGEvaluation A source).comp F)
    (fun x => target (obj x)) e
  exact { obj := obj
          map := L.map
          map_id := L.map_id
          map_comp := L.map_comp }

/-- 元の実関手とラベル作用の評価の比較は、全 Hom 複体に自然な閉同型。 -/
def inducedDGFunctorClosedConjugateIso :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    ((inducedDGEvaluation A source).comp F).onClosed ≅
      ((inducedDGFunctorClosedConjugate A source target F obj e).comp
        (inducedDGEvaluation A target)).onClosed := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  refine dgFunctorClosedComparisonIso A _ _ e (fun x y => ?_)
  simpa only [DGFunctor.comp, EnrichedFunctor.comp, inducedDGEvaluation,
    inducedDGFunctorClosedConjugate, Category.comp_id] using
    dgFunctorClosedConjugate_naturality A
      ((inducedDGEvaluation A source).comp F) (fun x => target (obj x)) e x y

end SerrePositivity.DifferentialGraded
end

end InducedClosedConjugate

/-! ## InducedClosedTransport（旧 SerrePositivity/DifferentialGraded/Functor/InducedClosedTransport.lean） -/

/-!
概要：任意ラベル族の等号移送を、評価値の閉同型による全 Hom 共役として表す。
方針：等号帰納と一般の共役恒等則を使い、元の豊穣関手の外延性へ接続する。
規約：任意の評価族に適用する。K-S 固有の提示対象宣言を import しない。
使われ方：小さい出発提示模型の全次数における厳密恒等・合成の検証。
-/

@[expose] public section InducedClosedTransport
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} [DGCategory A C]
  {I : Type w} (value : I → C)

lemma inducedDGHom_eqToHom {X X' Y Y' : I} (hx : X = X') (hy : Y = Y') :
    letI := inducedDGCategory A value
    eqToHom (congrArg₂ (homObject A I) hx hy) =
      enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun x => ForgetEnrichment.of (Complex A) (value x)) hx))
        (eqToIso (congrArg (fun x => ForgetEnrichment.of (Complex A) (value x)) hy)) := by
  subst X'
  subst Y'
  exact (enrichedClosedIsoConjugation_refl (Complex A)
    (ForgetEnrichment.of (Complex A) (value X))
    (ForgetEnrichment.of (Complex A) (value Y))).symm

lemma inducedDGFunctor_ext_of_closed_conjugation {J : Type t} [DGCategory A J] :
    letI := inducedDGCategory A value
    ∀ {F G : DGFunctor A J I} (h : ∀ x, F.obj x = G.obj x),
      (∀ x y, F.map x y ≫ enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun z => ForgetEnrichment.of (Complex A) (value z)) (h x)))
        (eqToIso (congrArg (fun z => ForgetEnrichment.of (Complex A) (value z)) (h y))) =
          G.map x y) → F = G := by
  let := inducedDGCategory A value
  intro F G h hm
  apply EnrichedFunctor.ext (Complex A) h
  intro x y
  exact (congrArg (fun k => F.map x y ≫ k)
    (inducedDGHom_eqToHom A value (h x) (h y))).trans (hm x y)

end SerrePositivity.DifferentialGraded
end

end InducedClosedTransport

/-! ## InducedClosedParameter（旧 SerrePositivity/DifferentialGraded/Functor/InducedClosedParameter.lean） -/

/-!
概要：任意のラベル族に沿う閉共役へ、全次数パラメータ自然変換も移す。
方針：評価で前合成した元の変換へ一般の閉共役を適用し、同じ Hom 複体を保持する。
規約：KST の依存は S 構成本体を含まない dg 一般論だけ。コピー・編集を行わない。
使われ方：κ-small 提示模型の dg 関手変数における豊穣作用の一般入口。
-/

@[expose] public section InducedClosedParameter
universe u v w i j

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] {I : Type i} {J : Type j}
  (source : I → C) (target : J → D) (F G : DGFunctor A C D)
  (objF objG : I → J)
  (eF : ∀ x, ForgetEnrichment.of (Complex A) (F.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (objF x)))
  (eG : ∀ x, ForgetEnrichment.of (Complex A) (G.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (objG x)))

/-- 同じ任意パラメータを、ラベル間の二つの実 dg 作用へ移す。 -/
def inducedDGFunctorClosedConjugateParameter {K : Complex A}
    (τ : DGFunctorParamTrans A C D K F G) :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    DGFunctorParamTrans A I J K
      (inducedDGFunctorClosedConjugate A source target F objF eF)
      (inducedDGFunctorClosedConjugate A source target G objG eG) := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  let T := dgFunctorClosedConjugateParameter A
    ((inducedDGEvaluation A source).comp F) ((inducedDGEvaluation A source).comp G)
    (fun x => target (objF x)) (fun x => target (objG x)) eF eG
    (dgFunctorParamPre A C D I (inducedDGEvaluation A source) τ)
  exact { app := T.app, naturality := T.naturality }

end SerrePositivity.DifferentialGraded
end

end InducedClosedParameter
