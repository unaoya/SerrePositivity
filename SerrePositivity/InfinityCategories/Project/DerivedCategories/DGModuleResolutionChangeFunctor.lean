module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeComposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
/-- 同じ入力と半自由出力を保ち、比較 cochain を指定後合成で移す実 dg 関手。 -/
def dgModuleResolutionChangeFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E G) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha
  map_id X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_identity R C E a hs hq ha X
  map_comp X Y Z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_composition R C E a hs hq ha X Y Z
/-- 同じ実比較 dg 関手は、元の実入力射影を厳密に保つ。 -/
lemma dgModuleResolutionChangeFunctor_source :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E G) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E G))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource, eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
/-- 同じ実比較 dg 関手は、元の実半自由出力射影も厳密に保つ。 -/
lemma dgModuleResolutionChangeFunctor_replacement :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E G) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E G))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement, eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
