module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionHom
/-!
概要：分解 Hom 複体への射を、実入力・実出力・比較ホモトピーから厳密に回収する。
方針：mapping cocone の実二射影と次数ごとの恒等分解を使う。
規約：全パラメータ複体からの射を扱う。使われ方：分解 dg 圏の合成則の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
/-- mapping cocone への実射は、鎖写像射影と比較 cochain で決まる。 -/
lemma dgMappingCocone_hom_ext {R : Type u} [CommRing R] {P Q K : Complex R}
    (d : P ⟶ Q) (f g : K ⟶ mappingCocone d)
    (hp : f ≫ mappingCocone.fst d = g ≫ mappingCocone.fst d)
    (ht : (Cochain.ofHom f).comp (mappingCocone.snd d) (zero_add (-1)) =
      (Cochain.ofHom g).comp (mappingCocone.snd d) (zero_add (-1))) : f = g := by
  apply HomologicalComplex.hom_ext
  intro j
  have hpj := congrArg (fun h ↦ h.f j) hp
  simp only [HomologicalComplex.comp_f] at hpj
  have htj := congrArg (fun h : Cochain K Q (-1) ↦ h.v j (j - 1) (by omega)) ht
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at htj
  have decomp (a : K ⟶ mappingCocone d) :
      a.f j = (a.f j ≫ (mappingCocone.fst d).f j) ≫
        (mappingCocone.inl d).v j j (add_zero j) +
      (a.f j ≫ (mappingCocone.snd d).v j (j - 1) (by omega)) ≫
        (mappingCocone.inr d).1.v (j - 1) j (by omega) := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      mappingCocone.id_X d j (j - 1) (by omega), Category.comp_id]
  rw [decomp f, decomp g, hpj, htj]
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (RightModule R E)) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
  (K : Complex R)
/-- 同じ分解 Hom 複体への実射から、指定比較ホモトピーを回収する。 -/
def dgModuleFunctorResolutionHomComparison
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y) :
    Cochain K (moduleHom R E X.replacement.val (F.obj Y.source)) (-1) :=
  (Cochain.ofHom f).comp
    (mappingCocone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X Y)) (zero_add _)
/-- 実二射影と比較ホモトピーが等しければ、全パラメータからの実射も等しい。 -/
lemma dgModuleFunctorResolutionHom_ext
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
    (ha : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F X Y)
    (hb : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
    (ht : dgModuleFunctorResolutionHomComparison R C E F X Y K f =
      dgModuleFunctorResolutionHomComparison R C E F X Y K g) : f = g := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X Y
  have hp : f ≫ mappingCocone.fst d = g ≫ mappingCocone.fst d := by
    apply biprod.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap, Category.assoc] using ha
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap, Category.assoc] using hb
  exact dgMappingCocone_hom_ext d f g hp ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories
