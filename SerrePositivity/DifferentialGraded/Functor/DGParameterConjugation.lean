module
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomUniversal

/-! # 全パラメータ付き自然変換の実閉零共役
概要：dg 自然変換のパラメータと全次数を保って、両端の関手を共役する。
方針：中間同型の tensor 合成での相殺を全豊穣自然性の四角形に適用する。
規約：単位パラメータに制限しない。使われ方：ラベル付き Perf の高次入力作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
section Enriched
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]
  {D : Type w} [EnrichedCategory V D] (F G : EnrichedFunctor V D C)
  (b c : D → C) (e : ∀ x, F.obj x ≅ b x) (f : ∀ x, G.obj x ≅ c x)

/-- 任意の中心パラメータを保持する、対象別同型による全豊穣自然変換の共役。 -/
def enrichedParameterConjugate {K : Center V} (τ : GradedNatTrans K F G) :
    GradedNatTrans K (enrichedFunctorClosedConjugate V F b e)
      (enrichedFunctorClosedConjugate V G c f) where
  app x := τ.app x ≫ enrichedClosedIsoConjugation V (e x) (f x)
  naturality x y := by
    change (K.2.β (x ⟶[V] y)).hom ≫
        ((F.map x y ≫ enrichedClosedIsoConjugation V (e x) (e y)) ⊗ₘ
          (τ.app y ≫ enrichedClosedIsoConjugation V (e y) (f y))) ≫
            eComp V (b x) (b y) (c y) =
      ((τ.app x ≫ enrichedClosedIsoConjugation V (e x) (f x)) ⊗ₘ
        (G.map x y ≫ enrichedClosedIsoConjugation V (f x) (f y))) ≫
          eComp V (b x) (c x) (c y)
    simp only [← tensorHom_comp_tensorHom_assoc]
    rw [enrichedClosedIsoConjugation_comp, enrichedClosedIsoConjugation_comp]
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ enrichedClosedIsoConjugation V (e x) (f y)) (τ.naturality x y)
end Enriched

variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] (F G : DGFunctor A D C)
  (b c : D → C)
  (e : ∀ x, ForgetEnrichment.of (Complex A) (F.obj x) ≅
    ForgetEnrichment.of (Complex A) (b x))
  (f : ∀ x, ForgetEnrichment.of (Complex A) (G.obj x) ≅
    ForgetEnrichment.of (Complex A) (c x))

/-- dg 関手の任意 K 自然変換を、同じ実閉零比較で共役した両端の間へ送る。 -/
def dgFunctorClosedConjugateParameter {K : Complex A}
    (τ : DGFunctorParamTrans A D C K F G) :
    DGFunctorParamTrans A D C K (dgFunctorClosedConjugate A F b e)
      (dgFunctorClosedConjugate A G c f) where
  app x := τ.app x ≫ enrichedClosedIsoConjugation (Complex A) (e x) (f x)
  naturality := (enrichedParameterConjugate (Complex A)
    (dgFunctorClosedTarget A F) (dgFunctorClosedTarget A G)
    (fun x => ForgetEnrichment.of (Complex A) (b x))
    (fun x => ForgetEnrichment.of (Complex A) (c x)) e f
    { app := τ.app, naturality := τ.naturality }).naturality

end SerrePositivity.KST.SConstruction
