module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.DifferentialGraded.Tensor.LeftColimits
public import SerrePositivity.DifferentialGraded.Tensor.YonedaRepresentative
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-! # graph延長とtensorの射影公式：Fubiniと全Hom自然なYoneda評価

## 概要
graph延長とtensorの射影公式：Fubiniと全Hom自然なYoneda評価。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma graphTensorYoneda_naturality (N : LeftModule A E) (x y : D) :
    (Fubini.leftModule A E D (functorGraph A D E F) N).map x y ≫
      homPostcompose _ (yonedaIso A E (F.obj y) N).hom =
    (F.comp N).map x y ≫ homPrecompose (yonedaIso A E (F.obj x) N).hom _ := by
  change ((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    rightHomMap A E (representable A (F.obj x)) (representable A (F.obj y)) N) ≫
      homPostcompose (obj A E (representable A (F.obj x)) N)
        (yonedaEvaluation A E (F.obj y) N) =
      (F.map x y ≫ N.map (F.obj x) (F.obj y)) ≫
        homPrecompose (yonedaEvaluation A E (F.obj x) N) (N.obj (F.obj y))
  simpa only [Category.assoc] using
    congrArg (fun k => F.map x y ≫ k)
      (yonedaEvaluation_representative_naturality A E N (F.obj x) (F.obj y))

/-- graphとのtensorのYoneda評価は全次数自然な左D加群同型。 -/
def graphTensorYonedaIso (N : LeftModule A E) :
    ForgetEnrichment.of (Complex A) (Fubini.leftModule A E D (functorGraph A D E F) N) ≅
      ForgetEnrichment.of (Complex A) (F.comp N) :=
  (leftModuleToRightOppositeFullyFaithful A D).preimageIso
    (X := ForgetEnrichment.of (Complex A)
      (Fubini.leftModule A E D (functorGraph A D E F) N))
    (Y := ForgetEnrichment.of (Complex A) (F.comp N))
    (moduleIsoMk A Dᵒᵖ
      (M := (Fubini.leftModule A E D (functorGraph A D E F) N).toRightOpposite)
      (N := LeftModule.toRightOpposite (F.comp N))
      (fun x => yonedaIso A E (F.obj x.unop.unop) N)
      (leftFamily_rightOpposite_naturality A D
        (M := Fubini.leftModule A E D (functorGraph A D E F) N) (N := F.comp N)
        (fun x => (yonedaIso A E (F.obj x) N).hom)
        (graphTensorYoneda_naturality A D E F N)))

@[simp]
lemma graphTensorYonedaIso_hom_eval (N : LeftModule A E) (d : D) :
    (leftModuleEvaluation A D d).map (graphTensorYonedaIso A D E F N).hom =
      (yonedaIso A E (F.obj d) N).hom :=
  moduleIsoMk_hom_eval A Dᵒᵖ
    (M := (Fubini.leftModule A E D (functorGraph A D E F) N).toRightOpposite)
    (N := LeftModule.toRightOpposite (F.comp N))
    (fun x => yonedaIso A E (F.obj x.unop.unop) N)
    (leftFamily_rightOpposite_naturality A D
      (M := Fubini.leftModule A E D (functorGraph A D E F) N) (N := F.comp N)
      (fun x => (yonedaIso A E (F.obj x) N).hom)
      (graphTensorYoneda_naturality A D E F N)) (op d)

/-- 任意の右D加群と左E加群について、延長とtensorを交換する実際の複体同型。 -/
def functorExtensionTensorIso (R : RightModule A D) (N : LeftModule A E) :
    obj A E ((dgModuleExtension A D E F).obj R) N ≅ obj A D R (F.comp N) :=
  (Fubini.iso A E D (functorGraph A D E F) R N).symm ≪≫
    (leftTensorFunctor A D R).mapIso (graphTensorYonedaIso A D E F N)

/-- 射影公式はR,graph,Nの順の三重生成元をYonedaの左作用で評価する。 -/
@[reassoc]
lemma rightι_functorExtensionTensorIso_hom (R : RightModule A D) (N : LeftModule A E)
    (e : E) (d : D) :
    Fubini.rightι A E D (functorGraph A D E F) R N e d ≫
        (functorExtensionTensorIso A D E F R N).hom =
      (R.obj (op d) ◁ leftAction A E N e (F.obj d)) ≫ ι A D R (F.comp N) d := by
  change Fubini.rightι A E D (functorGraph A D E F) R N e d ≫
    (Fubini.iso A E D (functorGraph A D E F) R N).inv ≫
      (leftTensorFunctor A D R).map (graphTensorYonedaIso A D E F N).hom = _
  rw [Fubini.rightι_iso_inv_assoc]
  change (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫
    ι A D R (Fubini.leftModule A E D (functorGraph A D E F) N) d ≫
      map A D (𝟙 (ForgetEnrichment.of (Complex A) R))
        (graphTensorYonedaIso A D E F N).hom = _
  have hm := ι_map A D (𝟙 (ForgetEnrichment.of (Complex A) R))
    (graphTensorYonedaIso A D E F N).hom d
  simp only [CategoryTheory.Functor.map_id, graphTensorYonedaIso_hom_eval, id_tensorHom] at hm
  refine (congrArg (fun k =>
    (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫ k) hm).trans ?_
  change (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫
    (R.obj (op d) ◁ yonedaEvaluation A E (F.obj d) N) ≫ ι A D R (F.comp N) d = _
  rw [← whiskerLeft_comp_assoc, ι_yonedaEvaluation]

/-- graph延長は右相対K-flat性を保つ。Homや左因子のflatnessは不要。 -/
lemma functorExtension_relativeKFlat (R : RightModule A D)
    (hR : moduleRelativeKFlat A D R) :
    moduleRelativeKFlat A E ((dgModuleExtension A D E F).obj R) := by
  intro N hN
  have hr := hR (F.comp N) (fun d => hN (F.obj d))
  exact cochainAcyclic_of_iso hr (functorExtensionTensorIso A D E F R N).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
