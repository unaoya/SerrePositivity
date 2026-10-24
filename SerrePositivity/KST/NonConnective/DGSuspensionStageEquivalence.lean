module
public import SerrePositivity.KST.NonConnective.DGSuspensionConnectedComparison

/-!
概要：同じ native loop 反復列の実隣接辺の可逆性を、元の実 BF 射の整数 π へ戻す。
方針：指定隣接辺の hSp 逆を実 BF 射に回収し、既存の同じ hSp 射の π 一致で両側逆を照合する。
規約：明示構造辺に条件付き。一般 Sp 判定や局所化 API は新設せず、この反復列に特殊化する。
使われ方：K-7 d の安定化範囲の監査。全整数安定化と非負整数安定化を区別する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance stageEquivalenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance stageEquivalenceHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (β : ∀ n : ℕ,
    SSet.Edge (coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))))

/-- 明示構造辺と同じ隣接辺の可逆性に条件付きで、同じ実遷移射は全整数 π 同型。 -/
theorem dgSuspensionNativeSequenceMap_piIsomorphism_of_isInvertible (n : ℕ)
    (hf : IsInvertibleEdge (coherentNerveEdge (dgSuspensionNativeSequenceMap R s A β n))) :
    OmegaSpectrum.PiIsomorphism (dgSuspensionNativeSequenceMap R s A β n) := by
  let f := dgSuspensionNativeSequenceMap R s A β n
  let q := Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated
  letI : IsIso q := hf
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective _ _ (inv q)
  let g := coherentNerveEdgeToHom (SSet.Edge.ofTruncated e)
  have hg : Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated = inv q := by
    rw [coherentNerveEdge_hom]
    exact he
  have hfg : Truncated.HomotopyCategory.homMk (coherentNerveEdge (f ≫ g)).toTruncated =
      Truncated.HomotopyCategory.homMk (coherentNerveEdge (𝟙 _)).toTruncated := by
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk (coherentNerveCompStruct f g).toTruncated,
      hg, IsIso.hom_inv_id, coherentNerveEdge_id]
    change 𝟙 _ = Truncated.HomotopyCategory.homMk (Truncated.Edge.id _)
    rw [Truncated.HomotopyCategory.homMk_id]
  have hgf : Truncated.HomotopyCategory.homMk (coherentNerveEdge (g ≫ f)).toTruncated =
      Truncated.HomotopyCategory.homMk (coherentNerveEdge (𝟙 _)).toTruncated := by
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk (coherentNerveCompStruct g f).toTruncated,
      hg, IsIso.inv_hom_id, coherentNerveEdge_id]
    change 𝟙 _ = Truncated.HomotopyCategory.homMk (Truncated.Edge.id _)
    rw [Truncated.HomotopyCategory.homMk_id]
  intro j
  have hp := sequentialHomotopyMap_eq_of_homMk_eq hfg j
  have hq := sequentialHomotopyMap_eq_of_homMk_eq hgf j
  rw [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_id] at hp hq
  exact ⟨Function.LeftInverse.injective (fun x => DFunLike.congr_fun hp x),
    Function.RightInverse.surjective (fun x => DFunLike.congr_fun hq x)⟩

end SerrePositivity.KST.NonConnective
