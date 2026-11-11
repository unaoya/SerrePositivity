module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NonpositiveUnitRestriction
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# 表現の鎖複体の指定増大

## 概要
HA 3.2.4.7 の二色係数について、指定された不変な増大を表現の鎖複体へ移す。

## 方針
零次成分を自明表現への射にし、忘却後の射を元の増大の制限と照合する。

## 規約
増大の零次成分は元の射と `singleObjXSelf` の合成を保持する。

## 使われ方
実際のテンソル係数の射影解像度の増大と擬同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
variable {A G : Type u} [CommRing A] [Group G]
  {K : CochainComplex (ModuleCat.{u} A) ℤ}

/-- 表現の複体の鎖次数への制限は、忘却後に元の制限と恒等成分で比較できる。 -/
def representationChainForgetIso (ρ : G →* End K) :
    ((forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).mapHomologicalComplex (.down ℕ)).obj
      ((representationCochainComplex ρ).restriction ComplexShape.embeddingDownNat) ≅
        K.restriction ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    simp
    rfl)

variable (ρ : G →* End K) (V : ModuleCat.{u} A)
  (f : K ⟶ (single (ModuleCat.{u} A) (.up ℤ) 0).obj V)
  (hf : ∀ g, (ρ g).asHom ≫ f = f)

/-- 不変な増大の零次成分を自明表現への射にする。 -/
def representationAugmentationZero :
    ((representationCochainComplex ρ).restriction ComplexShape.embeddingDownNat).X 0 ⟶
      Rep.trivial A G V :=
  Rep.ofHom ⟨(f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 V).hom).hom, fun g => by
    change ((ρ g).asHom.f 0 ≫ f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 V).hom).hom =
      (f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 V).hom).hom
    exact congrArg ModuleCat.Hom.hom (by
      simpa only [HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun k => k.f (0 : ℤ) ≫ (singleObjXSelf (.up ℤ) 0 V).hom) (hf g))⟩

/-- 指定された零次の増大は前の微分を消す。 -/
lemma representationAugmentationZero_d :
    ((representationCochainComplex ρ).restriction ComplexShape.embeddingDownNat).d 1 0 ≫
      representationAugmentationZero ρ V f hf = 0 := by
  apply (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map_injective
  change K.d (-1) 0 ≫ (f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 V).hom) = 0
  rw [← Category.assoc, ← f.comm (-1) 0]
  simp only [single_obj_d, comp_zero, zero_comp]

/-- 不変な指定増大を、表現の圏の鎖複体の増大にする。 -/
def representationChainAugmentation :
    (representationCochainComplex ρ).restriction ComplexShape.embeddingDownNat ⟶
      (ChainComplex.single₀ (Rep.{u} A G)).obj (Rep.trivial A G V) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨representationAugmentationZero ρ V f hf, representationAugmentationZero_d ρ V f hf⟩

/-- 表現の指定増大の忘却は、元の指定射の制限そのものである。 -/
lemma representationChainAugmentation_forget :
    let U := forget₂ (Rep.{u} A G) (ModuleCat.{u} A)
    (U.mapHomologicalComplex (.down ℕ)).map (representationChainAugmentation ρ V f hf) ≫
      (singleMapHomologicalComplex U (.down ℕ) 0).hom.app (Rep.trivial A G V) =
      (representationChainForgetIso ρ).hom ≫
        restrictionMap f ComplexShape.embeddingDownNat ≫ (nonpositiveSingleIso V).hom := by
  dsimp only
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  change (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map
    ((representationChainAugmentation ρ V f hf).f 0) ≫ _ =
      𝟙 (K.X 0) ≫ f.f 0 ≫ (nonpositiveSingleIso V).hom.f 0
  rw [show (representationChainAugmentation ρ V f hf).f 0 =
    representationAugmentationZero ρ V f hf from ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _,
    singleMapHomologicalComplex_hom_app_self, nonpositiveSingleIso_hom_f_zero]
  simp only [singleObjXSelf, singleObjXIsoOfEq, Category.id_comp]
  rfl

/-- 制限した元の指定射が擬同型なら、表現の圏の指定増大も擬同型である。 -/
lemma representationChainAugmentation_quasiIso
    [QuasiIso (restrictionMap f ComplexShape.embeddingDownNat)] :
    QuasiIso (representationChainAugmentation ρ V f hf) := by
  let U := forget₂ (Rep.{u} A G) (ModuleCat.{u} A)
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (representationChainAugmentation ρ V f hf) U]
  apply (quasiIso_iff_comp_right _
    ((singleMapHomologicalComplex U (.down ℕ) 0).hom.app (Rep.trivial A G V))).mp
  rw [representationChainAugmentation_forget]
  infer_instance

end SerrePositivity.EInfinity
