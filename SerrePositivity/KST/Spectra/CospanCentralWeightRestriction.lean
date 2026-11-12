module

public import SerrePositivity.KST.Spectra.CospanCentralWeightExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedExtensions

/-!
概要：両端固定の中央 anodyne な重みの制限は、実際の end の trivial Kan fibration。
方針：境界付きの重みを貼り、中央の pushout-product と両端の同型を延長補題に渡す。
規約：係数図式の中央の Kan 性だけを使う。使われ方：Hom–end と基点付き loop の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories

/-- 重みの指定成分が同型なら、境界を貼った相対直積の同じ成分も同型。 -/
lemma weightedCorner_isIso_at {I : Type u} [SmallCategory I]
    {W W' : I ⥤ SSet.{u}} (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B)
    (k : I) [IsIso (j.app k)] : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app k) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f k
  have topIso : IsIso (((curriedTensor SSet).map (j.app k)).app A) := by
    change IsIso (j.app k ▷ A)
    infer_instance
  have inrIso : IsIso P.inr := P.isPushout.isIso_inr_of_isIso
  have he : P.ι = inv P.inr ≫ (((curriedTensor SSet).map (j.app k)).app B) := by
    rw [← P.inr_ι]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  change IsIso P.ι
  rw [he]
  infer_instance

/-- 両端を固定した中央 anodyne な重みの制限は、全境界に対する持ち上げを持つ。 -/
lemma weightedSectionsPre_central_trivialKanFibration
    {W W' H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    [IsIso (j.app (AsSmall.up.obj .left))] [IsIso (j.app (AsSmall.up.obj .right))]
    (hj : anodyneExtensions (j.app (AsSmall.up.obj .one)))
    [KanComplex (H.obj (AsSmall.up.obj .one))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro t s sq
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j (boundary n).ι
  have hw : (j ▷ (Functor.const (AsSmall.{u} WalkingCospan)).obj (boundary n : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t =
      (W ◁ (Functor.const (AsSmall.{u} WalkingCospan)).map (boundary n).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry sq.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s) hw
  have leftCornerIso : IsIso (P.ι.app (AsSmall.up.obj .left)) :=
    weightedCorner_isIso_at j (boundary n).ι _
  have rightCornerIso : IsIso (P.ι.app (AsSmall.up.obj .right)) :=
    weightedCorner_isIso_at j (boundary n).ι _
  have hcenter : anodyneExtensions (P.ι.app (AsSmall.up.obj .one)) :=
    anodyneExtensions_pushoutObjObjι' (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j (boundary n).ι _) hj
  obtain ⟨b, hb⟩ := exists_cospan_extension_of_central_anodyne P.ι hcenter a
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W' H (boundary n : SSet.{u})).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry ((boundary n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ b := congrArg (fun f ↦ f ≫ b) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inl_desc _ _ _
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H (Δ[n] : SSet.{u})).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ b := congrArg (fun f ↦ f ≫ b) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inr_desc _ _ _

end SerrePositivity.KST.Spectra
