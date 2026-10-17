module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonModuleColimit
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements
public import SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit

/-! # 長さ零段階からの比較 cone の厳密な図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma complexConeMap_fst {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ) :
    (mappingCone.map f g a b h).f i ≫ (mappingCone.fst g).val.v i (i + 1) rfl =
      (mappingCone.fst f).val.v i (i + 1) rfl ≫ a.f (i + 1) := by
  change (Cochain.ofHom (mappingCone.map f g a b h)).v i i (add_zero i) ≫ _ = _
  rw [coneMapCochain_ofHom, coneMapCochain_fst_v]
  simp only [Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

lemma complexConeMap_snd {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ) :
    (mappingCone.map f g a b h).f i ≫ (mappingCone.snd g).v i i (add_zero i) =
      (mappingCone.snd f).v i i (add_zero i) ≫ b.f i := by
  change (Cochain.ofHom (mappingCone.map f g a b h)).v i i (add_zero i) ≫ _ = _
  rw [coneMapCochain_ofHom, coneMapCochain_snd_v, Cochain.ofHom_v]

lemma complexConeMap_f_injective {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ)
    (ha : Function.Injective (a.f (i + 1))) (hb : Function.Injective (b.f i)) :
    Function.Injective ((mappingCone.map f g a b h).f i) := by
  intro t s hts
  apply complexConeElement_ext A f i
  · apply ha
    have he := congrArg (fun z => (mappingCone.fst g).val.v i (i + 1) rfl z) hts
    simpa only [← ModuleCat.comp_apply, complexConeMap_fst] using he
  · apply hb
    have he := congrArg (fun z => (mappingCone.snd g).v i i (add_zero i) z) hts
    simpa only [← ModuleCat.comp_apply, complexConeMap_snd] using he

lemma complexConeMap_elementMk {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ)
    (t : P.X (i + 1)) (s : Q.X i) :
    (mappingCone.map f g a b h).f i (complexConeElementMk A f i t s) =
      complexConeElementMk A g i (a.f (i + 1) t) (b.f i s) := by
  apply complexConeElement_ext A g i
  · rw [← ModuleCat.comp_apply, complexConeMap_fst, ModuleCat.comp_apply,
      complexConeElementMk_fst, complexConeElementMk_fst]
  · rw [← ModuleCat.comp_apply, complexConeMap_snd, ModuleCat.comp_apply,
      complexConeElementMk_snd, complexConeElementMk_snd]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ℕ 図式の零段階から各段階へ向かう射を arrow 圏内の図式にする。 -/
def zeroSourceArrowDiagram (F : ℕ ⥤ ModuleCategory A D) :
    ℕ ⥤ Arrow (ModuleCategory A D) where
  obj n := Arrow.mk (F.map (homOfLE (Nat.zero_le n)))
  map {m n} f := Arrow.homMk (𝟙 _) (F.map f) (by
    change 𝟙 _ ≫ F.map (homOfLE (Nat.zero_le n)) =
      F.map (homOfLE (Nat.zero_le m)) ≫ F.map f
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    congr 1)
  map_id n := Arrow.hom_ext _ _ (by simp) (by simp)
  map_comp f g := Arrow.hom_ext _ _ (by simp) (by simp)

def zeroSourceArrowCocone (F : ℕ ⥤ ModuleCategory A D) (s : Cocone F) :
    Cocone (zeroSourceArrowDiagram A D F) where
  pt := Arrow.mk (s.ι.app 0)
  ι.app n := Arrow.homMk (𝟙 _) (s.ι.app n) (by
    change 𝟙 _ ≫ s.ι.app 0 = F.map (homOfLE (Nat.zero_le n)) ≫ s.ι.app n
    rw [Category.id_comp, s.w])
  ι.naturality {m n} f := by
    apply Arrow.hom_ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      rfl
    · change F.map f ≫ s.ι.app n = s.ι.app m ≫ 𝟙 _
      rw [Category.comp_id, s.w]

/-- 有限長の比較 cone からなる実際の加群図式。 -/
def lengthComparisonConeDiagram (S : Set D) (z : D) : ℕ ⥤ ModuleCategory A D :=
  zeroSourceArrowDiagram A D (lengthModuleDiagram A D S z) ⋙ moduleConeFunctor A D

/-- 商全体への比較 cone を頂点とする cocone。 -/
def lengthComparisonConeCocone (S : Set D) (z : D) :
    Cocone (lengthComparisonConeDiagram A D S z) :=
  (moduleConeFunctor A D).mapCocone
    (zeroSourceArrowCocone A D (lengthModuleDiagram A D S z) (lengthModuleCocone A D S z))

end SerrePositivity.DifferentialGraded.DGQuotient
