module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison

/-!
概要：h Sp の射と同型の整数 π の作用を、指定された元の BF 対象の群へ輸送する。
方針：既存の自然な piComparison で共役し、元の BF 射の作用との一致を使う。
規約：同じ h Sp の射を保持。使われ方：模型の全 fiber 頂点比較と構成済み群比較の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

variable {X Y Z : OmegaSpectrum.{u}}

def bfPiMap (m : obj X ⟶ obj Y) (j : ℤ) : CommGrpCat.of (homotopyGroup X j) ⟶
    CommGrpCat.of (homotopyGroup Y j) :=
  (piComparison X j).inv ≫ (piFunctor j).map m ≫ (piComparison Y j).hom

lemma bfPiMap_hom (f : X ⟶ Y) (j : ℤ) :
    bfPiMap (hom f) j = CommGrpCat.ofHom (homotopyMap f j) := by
  unfold bfPiMap
  rw [piComparison_naturality, Iso.inv_hom_id_assoc]

lemma bfPiMap_comp (f : obj X ⟶ obj Y) (g : obj Y ⟶ obj Z) (j : ℤ) :
    bfPiMap (f ≫ g) j = bfPiMap f j ≫ bfPiMap g j := by
  simp only [bfPiMap, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

def bfPiIso (e : obj X ≅ obj Y) (j : ℤ) : CommGrpCat.of (homotopyGroup X j) ≅
    CommGrpCat.of (homotopyGroup Y j) :=
  (piComparison X j).symm ≪≫ (piFunctor j).mapIso e ≪≫ piComparison Y j

lemma bfPiIso_hom (e : obj X ≅ obj Y) (j : ℤ) : (bfPiIso e j).hom = bfPiMap e.hom j := rfl

lemma bfPiIso_inv (e : obj X ≅ obj Y) (j : ℤ) : (bfPiIso e j).inv = bfPiMap e.inv j := by
  simp only [bfPiIso, bfPiMap, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

lemma piFunctor_map_from_bf (m : obj X ⟶ obj Y) (j : ℤ) :
    (piFunctor j).map m = (piComparison X j).hom ≫ bfPiMap m j ≫ (piComparison Y j).inv := by
  simp only [bfPiMap, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
