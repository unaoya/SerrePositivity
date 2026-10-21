module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionComparisonNaturality
/-!
概要：分解変更の実 Hom 鎖写像の二射影・比較 cochain と単位保存を照合する。
方針：同じ mapping cocone の全射影式と比較 cochain の一意性を使う。
規約：同じ全 Hom と元の実単位を保持する。使われ方：実分解変更 dg 関手。
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
variable (X Y : DGModuleFunctorResolutionObject R C E F)
/-- 同じ実入力 Hom への射影を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_source :
    dgModuleResolutionChangeHom R C E a hs hq ha X Y ≫
      dgModuleFunctorResolutionSourceHomMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y) =
      dgModuleFunctorResolutionSourceHomMap R C E F X Y := by
  simp only [dgModuleResolutionChangeHom, dgModuleFunctorResolutionSourceHomMap,
    ← Category.assoc, complexMappingCoconeMap_fst, Category.comp_id]
  rfl
/-- 同じ半自由出力 Hom への射影を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_replacement :
    dgModuleResolutionChangeHom R C E a hs hq ha X Y ≫
      dgModuleFunctorResolutionReplacementHomMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y) =
      dgModuleFunctorResolutionReplacementHomMap R C E F X Y := by
  simp only [dgModuleResolutionChangeHom, dgModuleFunctorResolutionReplacementHomMap,
    ← Category.assoc, complexMappingCoconeMap_fst, Category.comp_id]
  rfl
/-- 比較 cochain は、終点の同じ比較射による後合成そのもの。 -/
lemma dgModuleResolutionChangeHom_comparison :
    dgModuleFunctorResolutionHomComparison R C E G
      (dgModuleResolutionChangeObject R C E a hs hq X)
      (dgModuleResolutionChangeObject R C E a hs hq Y) _
      (dgModuleResolutionChangeHom R C E a hs hq ha X Y) =
    (dgModuleFunctorResolutionPrimitive R C E F X Y).comp
      (Cochain.ofHom (moduleHomPostcompose R E X.replacement.val
        (F.obj Y.source) (G.obj Y.source) (a Y.source))) (add_zero (-1)) :=
  complexMappingCoconeMap_snd _ _ _ _ _
omit Y in
/-- 同じ実 Hom 鎖写像は、実分解 dg 圏の同じ実単位を保存する。 -/
lemma dgModuleResolutionChangeHom_identity :
    dgModuleFunctorResolutionIdentity R C E F X ≫
      dgModuleResolutionChangeHom R C E a hs hq ha X X =
    dgModuleFunctorResolutionIdentity R C E G (dgModuleResolutionChangeObject R C E a hs hq X) := by
  apply dgModuleFunctorResolutionHom_ext R C E G
  · rw [Category.assoc, dgModuleResolutionChangeHom_source,
      dgModuleFunctorResolutionIdentity_source, dgModuleFunctorResolutionIdentity_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionChangeHom_replacement,
      dgModuleFunctorResolutionIdentity_replacement, dgModuleFunctorResolutionIdentity_replacement]
    rfl
  · have hz : (Cochain.ofHom (dgModuleFunctorResolutionIdentity R C E F X)).comp
        (dgModuleFunctorResolutionPrimitive R C E F X X) (zero_add (-1)) = 0 :=
      dgModuleFunctorResolutionIdentity_comparison R C E F X
    rw [dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionChangeHom_comparison, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      hz, Cochain.zero_comp, dgModuleFunctorResolutionIdentity_comparison]
end SerrePositivity.InfinityCategories
