module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornFrontBoundary
public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornLastPath

/-!
概要：最終外側ホーンの最終既知区間から、実際の後合成写像を回収する。
方針：隣接 Path の単位同型で射を抽出し、native 合成面の式を照合する。
規約：前半の未知 Hom は任意の写像として扱い、存在や境界可換性を仮定しない。
使われ方：HTT 5.2.4.6 の前半全境界と延長した後半 Hom の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 最後の既知区間 Hom の零単体から、元の最終区間の通常の射を回収する。 -/
def finalHornLastArrow : hornObj σ (finalHornPenultimate n) ⟶ hornObj σ (Fin.last (n + 2)) :=
  (eHomEquiv SSet).symm ((finalHornLastPathIso n).hom ≫
    finalHornKnownIntervalHom σ (finalHornPenultimate n) (Fin.last (n + 2))
      (le_of_lt (finalHornPenultimate_lt_last n))
      (Or.inl (ne_of_gt (finalHornPenultimate_pos n))))

/-- 回収した最終区間の射の豊穣像は、元の同じ既知区間 Hom の値に一致する。 -/
lemma finalHornLastArrow_eHom : eHomEquiv SSet (finalHornLastArrow σ) =
    (finalHornLastPathIso n).hom ≫
      finalHornKnownIntervalHom σ (finalHornPenultimate n) (Fin.last (n + 2))
        (le_of_lt (finalHornPenultimate_lt_last n))
        (Or.inl (ne_of_gt (finalHornPenultimate_pos n))) :=
  (eHomEquiv SSet).apply_symm_apply _

/-- 前半 Path と合成面の同型は、元の最終区間の射による実際の後合成を与える。 -/
lemma finalHornFrontThroughIso_postcomposition
    (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (hornObj σ 0) (hornObj σ (finalHornPenultimate n))) :
    (finalHornFrontThroughIso n).hom ≫
      (pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).inv ≫
          (f ⊗ₘ finalHornKnownIntervalHom σ (finalHornPenultimate n) (Fin.last (n + 2))
            (le_of_lt (finalHornPenultimate_lt_last n))
            (Or.inl (ne_of_gt (finalHornPenultimate_pos n)))) ≫
              SimplicialCategory.sHomComp (hornObj σ 0)
                (hornObj σ (finalHornPenultimate n)) (hornObj σ (Fin.last (n + 2))) =
      f ≫ eHomWhiskerLeft SSet (hornObj σ 0) (finalHornLastArrow σ) := by
  simp only [finalHornFrontThroughIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  unfold eHomWhiskerLeft
  rw [finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
