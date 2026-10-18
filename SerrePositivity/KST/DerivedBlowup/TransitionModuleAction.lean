module

public import SerrePositivity.KST.DerivedBlowup.GradedNaturalWhiskering
public import SerrePositivity.DifferentialGraded.Module.Left
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-!
概要：KST §3.1 の指定の全次数自然変換を実際の図式加群に作用させる。
方針：二重 opposite の dg 比較と前後の whiskering で、右 dg 加群の全次数自然変換へ送る。
規約：図式加群は係数圏の opposite 上の右加群として扱う。
使われ方：canonical な局所制限の比較射を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

/-- 概要：指定の単位パラメータの全次数自然変換を右 dg 加群へ作用させる。
方針：二重 opposite と加群の豊穣関手による後合成、二重 unop による前合成を使う。
規約：KST §3.1。使われ方：指定単位矢からの局所加群の比較。 -/
def transitionModuleParam {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    (M : RightModule R Dᵒᵖ) :
    ModuleParamTrans R Cᵒᵖ (𝟙_ (Complex R))
      (restrictModule R Cᵒᵖ Dᵒᵖ F.op.op M) (restrictModule R Cᵒᵖ Dᵒᵖ G.op.op M) := by
  let σ := dgGradedWhiskerLeft (dgDoubleUnop R C)
    (dgGradedWhiskerRight (dgGradedWhiskerRight τ (dgDoubleOpposite R D)) M.toFunctor)
  refine { app := fun x => σ.app x, naturality := ?_ }
  intro x y
  have h := σ.naturality x y
  dsimp only [restrictModule, RightModule.toFunctor, DGFunctor.comp, EnrichedFunctor.comp,
    dgDoubleUnop, dgDoubleOpposite, DGFunctor.op] at h ⊢
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using h

variable [Small.{u} C]

/-- 概要：指定の全次数自然変換から得た実際の閉零 dg 加群射。
方針：全次数 Hom end の普遍性で単位パラメータの自然変換を射にする。
規約：KST §3.1。使われ方：canonical な局所加群の比較射。 -/
def transitionModuleMorphism {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    (M : RightModule R Dᵒᵖ) :
    ForgetEnrichment.of (Complex R) (restrictModule R Cᵒᵖ Dᵒᵖ F.op.op M) ⟶
      ForgetEnrichment.of (Complex R) (restrictModule R Cᵒᵖ Dᵒᵖ G.op.op M) :=
  ForgetEnrichment.homOf (Complex R)
    ((moduleHomEquiv R Cᵒᵖ (𝟙_ (Complex R)) _ _).symm (transitionModuleParam τ M))

/-- 概要：指定の全次数自然変換を加群へ作用させた通常複体の成分。
方針：加群の Hom 写像で指定単位矢を送り、単位パラメータから通常の鎖写像へ戻す。
規約：KST §3.1。使われ方：canonical な比較の成分と自然性の計算。 -/
def transitionModuleComponent {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    (M : RightModule R Dᵒᵖ) (x : C) :
    M.obj (op (op (F.obj x))) ⟶ M.obj (op (op (G.obj x))) :=
  mapFromUnit R _ _ (τ.app x ≫ M.map (op (op (F.obj x))) (op (op (G.obj x))))

/-- 概要：構成した dg 加群射の評価は指定単位矢の実際の加群作用に一致する。
方針：全次数 Hom end の単位パラメータ同値の逆元律を評価する。
規約：KST §3.1。使われ方：加群比較の自然性と canonical な経路の検証。 -/
theorem transitionModuleMorphism_eval {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    (M : RightModule R Dᵒᵖ) (x : C) :
    (moduleEvaluation R Cᵒᵖ (op x)).map (transitionModuleMorphism τ M) =
      transitionModuleComponent τ M x := by
  have hc : moduleClosedHomEquiv R Cᵒᵖ _ _ (transitionModuleMorphism τ M) =
      transitionModuleParam τ M :=
    Equiv.apply_symm_apply (moduleHomEquiv R Cᵒᵖ (𝟙_ (Complex R)) _ _) _
  have ha := congrArg (fun σ => closedTransApp R σ (op (op x))) hc
  rw [moduleClosedHomEquiv_app] at ha
  change (moduleEvaluation R Cᵒᵖ (op x)).map (transitionModuleMorphism τ M) =
    mapFromUnit R _ _ ((τ.app x ≫ 𝟙 _) ≫ M.map (op (op (F.obj x))) (op (op (G.obj x)))) at ha
  simpa only [Category.comp_id, transitionModuleComponent] using ha

end SerrePositivity.KST.DerivedBlowup
