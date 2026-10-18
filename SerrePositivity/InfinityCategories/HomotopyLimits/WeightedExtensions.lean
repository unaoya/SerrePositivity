module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCorner
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedFunctor
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan

/-!
概要：図式への anodyne な延長から重み付き end の Kan 性と重みの制限の同値性を得る。
方針：ホーンは重みとの直積、境界付きの制限は pushout-product へ転置する。
規約：延長操作の存在は入力とし、個々の図式で別に証明する。
使われ方：Kerodon 7.5.3、7.5.4.6 の isofibrant な図式の end。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：成分ごとの anodyne な射に沿う全ての自然変換を延長できる図式の end は Kan。
方針：end のホーンを重み付き自然変換に移し、重みとホーン包含の直積に沿って延長する。
規約：延長性 hH は具体的な図式の持ち上げで検証する入力である。
使われ方：Kerodon 7.5.3、有限の isofibrant 図式の切断空間。 -/
lemma weightedSections_kanComplex_of_extensions (W H : I ⥤ SSet.{u})
    (hH : ∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
      (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a) :
    KanComplex (weightedSections W H) := by
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  let j := W ◁ (Functor.const I).map (horn (n + 1) i).ι
  have hj (k : I) : anodyneExtensions (j.app k) :=
    (anodyneExtensions.horn_ι i).whiskerLeft (W.obj k)
  obtain ⟨b, hb⟩ := hH j hj (weightedSectionsUncurry σ)
  refine ⟨weightedSectionsLift b, ?_⟩
  apply (weightedSectionsHomEquiv W H (horn (n + 1) i : SSet.{u})).injective
  change weightedSectionsUncurry ((horn (n + 1) i).ι ≫ weightedSectionsLift b) = _
  rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
  exact hb

/-- 概要：成分ごとの anodyne な延長ができる図式に対して重みの anodyne な制限は trivial Kan fibration。
方針：境界付きの二つの自然変換を pushout 上で貼り、その anodyne な相対直積から延長する。
規約：図式のモデル構造は要求せず、明示した延長性だけを使う。
使われ方：Kerodon 7.5.3、isofibrant な図式の重みの比較。 -/
lemma weightedSectionsPre_trivialKanFibration_of_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    (hH : ∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
      (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a) :
    TrivialKanFibration (weightedSectionsPre j H) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro t s sq
  let P := weightedCorner j (boundary n).ι
  have hw : (j ▷ (Functor.const (I)).obj (boundary n : SSet.{u})) ≫
        weightedSectionsUncurry t =
      (W ◁ (Functor.const (I)).map (boundary n).ι) ≫
        weightedSectionsUncurry s := by
    have h := congrArg weightedSectionsUncurry sq.w
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (weightedSectionsUncurry t) (weightedSectionsUncurry s) hw
  obtain ⟨b, hb⟩ := hH P.ι
    (weightedCorner_obj_anodyne j hj (boundary n).ι) a
  refine CommSq.HasLift.mk' { l := weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (weightedSectionsHomEquiv W' H (boundary n : SSet.{u})).injective
    change weightedSectionsUncurry ((boundary n).ι ≫ weightedSectionsLift b) = _
    rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inl_desc _ _ _
  · apply (weightedSectionsHomEquiv W H (Δ[n] : SSet.{u})).injective
    change weightedSectionsUncurry (weightedSectionsLift b ≫ weightedSectionsPre j H) = _
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inr_desc _ _ _

/-- 概要：成分ごとの anodyne な延長ができる図式の end の重みの制限はホモトピー同値。
方針：両側の end の Kan 性と全境界の持ち上げを使って実際のホモトピー逆を得る。
規約：hH の検証は各適用先で行う。
使われ方：Kerodon 7.5.3、7.5.4.6 の標準比較の重みの変更。 -/
lemma weightedSectionsPre_homotopyEquivalence_of_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    (hH : ∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
      (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre j H) := by
  have := weightedSections_kanComplex_of_extensions W H hH
  have := weightedSections_kanComplex_of_extensions W' H hH
  have := weightedSectionsPre_trivialKanFibration_of_extensions (H := H) j hj hH
  exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
