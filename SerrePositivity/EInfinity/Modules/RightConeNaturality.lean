module
public import SerrePositivity.EInfinity.Modules.RightConeComponents

/-!
概要：終端を除いた元の単体成分は、指定 augmentation と全次数で厳密に両立する。
方針：最後の退化は終端を避ける集合上で単射であり、その像へ元の整合式を適用する。
規約：HA Construction 1.3.1.6・1.3.1.13、同じ元の cochain と chain map。使われ方：終端側 HA の二点右切断。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeIndex_recover {n : ℕ} (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    ((Fin.last n).predAboveOrderHom i).castSucc = i := by
  induction i using Fin.lastCases with
  | last => exact False.elim (hi rfl)
  | cast i =>
    change ((Fin.last n).predAbove i.castSucc).castSucc = i.castSucc
    rw [Fin.predAbove_last_castSucc]

lemma moduleRightConeIndex_injOn {n : ℕ} (I : Finset (Fin (n + 2)))
    (b : Fin (n + 2)) (hI : 2 ≤ I.card) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hbl : b ≠ Fin.last (n + 1)) :
    Set.InjOn (Fin.last n).predAboveOrderHom (I : Set (Fin (n + 2))) := by
  have hn : ∀ i ∈ I, i ≠ Fin.last (n + 1) := by
    intro i hi hil
    apply hbl
    apply le_antisymm (Fin.le_last _)
    rw [hb, ← hil]
    exact I.le_max' i hi
  intro i hi j hj hij
  have h := congrArg Fin.castSucc hij
  rwa [moduleRightConeIndex_recover i (hn i hi),
    moduleRightConeIndex_recover j (hn j hj)] at h

lemma moduleRightConeData_front_compose {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (n + 1)) :
    compose A (closedHomEquiv A (RightModule A D) _ _ (η.app ((Fin.last n).predAboveOrderHom b))).val
      ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk)
      (add_zero k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a)) k := by
  have hi := moduleRightConeIndex_injOn I b hI hb hbl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  exact η.hom_naturality _ _ _ _ _ _ _ _

end SerrePositivity.EInfinity.Modules
