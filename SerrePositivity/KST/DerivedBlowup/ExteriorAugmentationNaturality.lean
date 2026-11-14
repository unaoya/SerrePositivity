module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.ExteriorQuotientAugmentation

/-!
概要：KST Def3.1 の標準添加射の係数代数に関する自然性。
方針：単一複体への射を次数0で比較し、代数準同型の係数保存へ帰着する。
規約：解消性を仮定しない自然性と、係数商同型による擬同型の移送を分ける。
使われ方：標準添加射を関係式商から通常の普遍チャート環へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R S T M : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [AddCommGroup M] [Module R M]

/-- 概要：標準添加射は係数代数準同型と可換。
方針：次数0の係数構造射を比較する。
規約：KST Def3.1。使われ方：関係式商の表示変更に沿う標準添加射の移送。 -/
theorem exteriorKoszulAugmentation_naturality (d : M →ₗ[R] R)
    (hS : ∀ m, algebraMap R S (d m) = 0) (hT : ∀ m, algebraMap R T (d m) = 0)
    (f : S →ₐ[R] T) :
    exteriorKoszulAugmentation d hT = exteriorKoszulAugmentation d hS ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (ModuleCat.ofHom f.toLinearMap) := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R T)).hom).mp
  simp only [exteriorKoszulAugmentation, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change exteriorCochainAugmentationComponent (S := T) d 0 z =
    f (exteriorCochainAugmentationComponent (S := S) d 0 z)
  rw [exteriorCochainAugmentationComponent_zero, exteriorCochainAugmentationComponent_zero]
  exact (f.commutes _).symm

/-- 概要：係数代数が微分像の商なら標準添加射は高次消滅から擬同型となる。
方針：標準商添加射の擬同型性を代数同型と自然性で移す。
規約：KST Lemma3.6。使われ方：普遍チャートの標準添加射の解消性。 -/
theorem exteriorKoszulAugmentation_quasiIso_of_quotient (d : M →ₗ[R] R)
    (hS : ∀ m, algebraMap R S (d m) = 0)
    (e : (R ⧸ LinearMap.range d) ≃ₐ[R] S)
    (h : ∀ q : ℤ, q ≠ 0 → IsZero ((exteriorKoszulCochain d).homology q)) :
    QuasiIso (exteriorKoszulAugmentation d hS) := by
  rw [exteriorKoszulAugmentation_naturality d (exteriorDifferential_quotient_zero d) hS
    e.toAlgHom]
  have : QuasiIso (exteriorKoszulAugmentation d (exteriorDifferential_quotient_zero d)) :=
    exteriorQuotientAugmentation_quasiIso d h
  have : IsIso (ModuleCat.ofHom e.toAlgHom.toLinearMap) :=
    e.toLinearEquiv.toModuleIso.isIso_hom
  have : IsIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (ModuleCat.ofHom e.toAlgHom.toLinearMap)) := inferInstance
  exact quasiIso_comp _ _

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 3.4" (partial := component) "仮定：係数環の有限列と Koszul の負次数消滅を要求（Lean が強い）。結論：外積 Koszul の商環への増大が準同型。正則列に沿う閉部分スキームの導来引き戻しを組み立てる前の局所比較（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exteriorKoszulAugmentation_quasiIso_of_quotient
