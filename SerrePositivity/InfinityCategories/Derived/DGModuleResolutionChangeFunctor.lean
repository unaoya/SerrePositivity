module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeComposition
/-!
概要：全 Hom 自然な次数別全射準同型に沿う、実分解 dg 圏の比較関手。
方針：同じ実対象・Hom 鎖写像・単位合成保存を束ね、両射影の厳密等式を証明する。
規約：元の入力と半自由出力を変更しない。使われ方：実出力分解 ∞ 関手の変更比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
/-- 同じ入力と半自由出力を保ち、比較 cochain を指定後合成で移す実 dg 関手。 -/
def dgModuleResolutionChangeFunctor :
    DGFunctor R (DGModuleFunctorResolutionObject R C E F)
      (DGModuleFunctorResolutionObject R C E G) where
  obj := dgModuleResolutionChangeObject R C E a hs hq
  map := dgModuleResolutionChangeHom R C E a hs hq ha
  map_id X := dgModuleResolutionChangeHom_identity R C E a hs hq ha X
  map_comp X Y Z := dgModuleResolutionChangeHom_composition R C E a hs hq ha X Y Z
/-- 同じ実比較 dg 関手は、元の実入力射影を厳密に保つ。 -/
lemma dgModuleResolutionChangeFunctor_source :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionSource R C E G) = dgModuleFunctorResolutionSource R C E F := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionSource R C E G))
    (G := dgModuleFunctorResolutionSource R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    dgModuleFunctorResolutionSource, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
/-- 同じ実比較 dg 関手は、元の実半自由出力射影も厳密に保つ。 -/
lemma dgModuleResolutionChangeFunctor_replacement :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionReplacement R C E G) =
        dgModuleFunctorResolutionReplacement R C E F := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionReplacement R C E G))
    (G := dgModuleFunctorResolutionReplacement R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    dgModuleFunctorResolutionReplacement, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
end SerrePositivity.InfinityCategories
