module
public import SerrePositivity.KST.SConstruction.DGPerfectEndIsoComparison

/-! # 実 perfect 像の End と元の代表対象 End の比較
概要：指定 dg 関手の実 perfect 像と代表加群の閉同型を、元の対象 End 比較へ束ねる。
方針：同じ関手の End 制限と、型を固定した既存の perfect End 比較を合成する。
規約：像の対象・全 Hom を保持。使われ方：元の小終域から生の終域への End 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {C : Type w} [DGCategory R C] (F : DGFunctor R C (PerfectDGModule R E))
  (x : C) (b : E)
  (e : ForgetEnrichment.of (Complex R) (F.obj x).val ≅
    ForgetEnrichment.of (Complex R) (representable R b))

/-- 同じ実 perfect 像を通し、元の対象 End へ戻す全 Hom 鎖写像。 -/
def dgPerfectImageEndIsoHom : homObject R C x x ⟶ homObject R E b b :=
  F.map x x ≫ dgPerfectEndIsoObjectHom R E (F.obj x) b e

/-- 同じ実 perfect 像と指定閉同型を使う元の全 End の間の実 dg 関手。 -/
def dgPerfectImageEndIsoFunctor : DGFunctor R (EndomorphismObject x) (EndomorphismObject b) :=
  (endomorphismMap R F x).comp (dgPerfectEndIsoObjectFunctor R E (F.obj x) b e)

/-- 同じ実 End 関手の全 Hom 作用は、型を固定した同じ実比較。 -/
lemma dgPerfectImageEndIsoFunctor_map (a c : EndomorphismObject x) :
    (dgPerfectImageEndIsoFunctor R E F x b e).map a c =
      dgPerfectImageEndIsoHom R E F x b e := by
  change F.map x x ≫ (dgPerfectEndIsoObjectFunctor R E (F.obj x) b e).map _ _ = _
  exact congrArg (fun f => F.map x x ≫ f)
    (dgPerfectEndIsoObjectFunctor_map R E (F.obj x) b e _ _)

end SerrePositivity.KST.SConstruction
