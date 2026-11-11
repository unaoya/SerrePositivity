module
public import SerrePositivity.KST.SConstruction.DGGluingLeftAxisImageGeneration

/-! # 指定対角の左成分の生成条件による二軸像の生成
概要：指定対角の左成分が C の Perf を生成すれば、同じ対角像と右軸像が全像を生成する。
方針：左軸関手の実導来延長へ条件を戻し、D の既存 Perfect 生成判定を使う。
規約：左成分の生成条件は明示入力。使われ方：具体的 dg 四角形と元の商 End の比較。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) E)
  {A : Type t} [DGCategory R A] (j : DGFunctor R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToDerived R E
local notation "LF" => DGFunctor.comp (dgGluingLeftAxis R C D M zd hd) F
local instance : (dgDerivedExtension R C E (LF)).CommShift ℤ :=
  dgDerivedExtensionCommShift R C E (LF)
local instance : (dgDerivedExtension R C E (LF)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated R C E (LF)

include hc hd in
/-- 指定左成分の Perf 生成条件から、同じ対角像と右軸像による全左軸像の生成を得る。 -/
lemma dgGluingLeftAxis_image_mem_of_diagonal
    (hgen : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C)
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts]
    (hR : ∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc d))))))
    (hJ : ∀ a : A, P ((Q).obj (ForgetEnrichment.of (Complex R) (representable R (F.obj
      (j.obj a)))))) (c : C) : P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingLeftAxisObject R C D M zd c))))) := by
  let H := P.inverseImage (dgDerivedExtension R C E (LF))
  have : H.IsTriangulated := by dsimp [H]; infer_instance
  have : H.IsClosedUnderIsomorphisms := by dsimp [H]; infer_instance
  have : H.IsStableUnderRetracts :=
    ⟨fun r hy => P.prop_of_retract (r.map (dgDerivedExtension R C E (LF))) hy⟩
  have hs : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) ≤ H := by
    apply modulePerfectOver_le_of_generators R C H
    rintro y ⟨a, rfl⟩
    exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R C E (LF) (j.obj a).left).symm
      (dgGluingLeftAxis_image_mem_of_right_middle R C D M zc hc zd hd E F P
        (j.obj a) (hR (j.obj a).right) (hJ a))
  have hall : modulePerfect R C ≤ H := hgen ▸ hs
  have h := hall _ (modulePerfectOver_representable R C c (Set.mem_univ _))
  exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R C E (LF) c) h

include hc hd in
/-- 同じ指定対角の左成分の生成条件により、全 dg 関手像の Perf を判定する。 -/
lemma dgGluingPerfectOver_image_le_of_diagonal
    (hgen : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C)
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts]
    (hR : ∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc d))))))
    (hJ : ∀ a : A, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (j.obj a)))))) :
    modulePerfectOver R E (Set.range F.obj) ≤ P :=
  (dgGluingPerfectOver_image_le_iff_axes R C D M zc hc zd hd E F P).mpr
    ⟨hR, dgGluingLeftAxis_image_mem_of_diagonal R C D M zc hc zd hd E F j hgen P hR hJ⟩

end SerrePositivity.KST.SConstruction
