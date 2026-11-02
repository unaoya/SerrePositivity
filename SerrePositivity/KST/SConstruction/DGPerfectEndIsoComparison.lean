module
public import SerrePositivity.KST.SConstruction.DGEndIsoConjugation
public import SerrePositivity.KST.SConstruction.DGEndYonedaInverse
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-! # 元の perfect 加群の End と代表対象の End の比較
概要：指定した実閉同型を使い、perfect 加群の全 End を元の代表対象の End に送る。
方針：充満包含・元の閉共役・元の Yoneda 逆同型を、抽象加群の型で組み立てる。
規約：商・局所化の API を作らない。使われ方：同じ四角形の具体的 End 比較への特殊化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (M : PerfectDGModule R E) (b : E)
  (e : ForgetEnrichment.of (Complex R) M.val ≅
    ForgetEnrichment.of (Complex R) (representable R b))

/-- 元の閉共役を、元の perfect Hom から右加群 Hom への同じ鎖写像として読む。 -/
def dgPerfectEndIsoModuleHom :
    homObject R (PerfectDGModule R E) M M ⟶
      homObject R (RightModule R E) (representable R b) (representable R b) :=
  dgEndIsoHom R (D := RightModule R E) e

/-- 元の Yoneda 同型で戻す、同じ perfect End から元の対象 End への実鎖写像。 -/
def dgPerfectEndIsoObjectHom : homObject R (PerfectDGModule R E) M M ⟶ homObject R E b b :=
  dgPerfectEndIsoModuleHom R E M b e ≫ (dgYonedaIso R b (representable R b)).hom

/-- 同じ perfect 加群の End から元の代表加群の End への実 dg 関手。 -/
def dgPerfectEndIsoModuleFunctor :
    DGFunctor R (EndomorphismObject M) (EndomorphismObject (representable R b)) :=
  (endomorphismMap R (perfectDGModuleInclusion R E Set.univ) M).comp
    (dgEndIsoFunctor R (D := RightModule R E) e)

/-- 同じ加群 End 関手の全 Hom 写像は、構成済みの同じ閉共役。 -/
lemma dgPerfectEndIsoModuleFunctor_map (x y : EndomorphismObject M) :
    (dgPerfectEndIsoModuleFunctor R E M b e).map x y =
      dgPerfectEndIsoModuleHom R E M b e := by
  change 𝟙 _ ≫ dgEndIsoHom R (D := RightModule R E) e = _
  exact Category.id_comp _

/-- 同じ perfect 加群の End を元の dg 対象の End へ送る実 dg 関手。 -/
def dgPerfectEndIsoObjectFunctor : DGFunctor R (EndomorphismObject M) (EndomorphismObject b) :=
  (dgPerfectEndIsoModuleFunctor R E M b e).comp (dgEndYonedaInverse R E b)

/-- 同じ対象 End 関手の全 Hom 写像は、型を固定した同じ実比較 Hom。 -/
lemma dgPerfectEndIsoObjectFunctor_map (x y : EndomorphismObject M) :
    (dgPerfectEndIsoObjectFunctor R E M b e).map x y =
      dgPerfectEndIsoObjectHom R E M b e := by
  change (dgPerfectEndIsoModuleFunctor R E M b e).map x y ≫
    (dgYonedaIso R b (representable R b)).hom = _
  rw [dgPerfectEndIsoModuleFunctor_map]
  rfl

end SerrePositivity.KST.SConstruction
