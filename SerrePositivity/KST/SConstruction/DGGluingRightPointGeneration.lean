module
public import SerrePositivity.KST.SConstruction.DGGluingAxesImageGeneration

/-! # 元の右成分の指定生成対象からの右軸像の生成
概要：元の D が指定対象 b から Perf 生成されれば、同じ右軸像も b の像から生成される。
方針：元の右軸と実 dg 関手を合成し、D の既存導来延長と生成判定を使う。
規約：指定対象と元の関手を保持。使われ方：K-10 c の同じ右対象の商 End。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) E) (b : D)
local notation "Q" => moduleToDerived R E
local notation "RF" => DGFunctor.comp (dgGluingRightAxis R C D M zc hc) F
local instance : (dgDerivedExtension R D E (RF)).CommShift ℤ :=
  dgDerivedExtensionCommShift R D E (RF)
local instance : (dgDerivedExtension R D E (RF)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated R D E (RF)

include hc in
/-- 元の指定右対象の Perf 生成条件から、同じ右軸像の全対象を生成する。 -/
lemma dgGluingRightAxis_image_mem_of_point
    (hgen : modulePerfectOver R D {b} = modulePerfect R D)
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts]
    (hb : P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc b)))))) (d : D) :
    P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc d))))) := by
  let H := P.inverseImage (dgDerivedExtension R D E (RF))
  have : H.IsTriangulated := by dsimp [H]; infer_instance
  have : H.IsClosedUnderIsomorphisms := by dsimp [H]; infer_instance
  have : H.IsStableUnderRetracts :=
    ⟨fun r hy => P.prop_of_retract (r.map (dgDerivedExtension R D E (RF))) hy⟩
  have hs : modulePerfectOver R D {b} ≤ H := by
    apply modulePerfectOver_le_of_generators R D H
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R D E (RF) y).symm hb
  have hall : modulePerfect R D ≤ H := hgen ▸ hs
  have h := hall _ (modulePerfectOver_representable R D d (Set.mem_univ _))
  exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R D E (RF) d) h

end SerrePositivity.KST.SConstruction
