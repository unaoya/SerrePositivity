module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanSectionsIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.WeightedNerveLeftFibration

/-!
概要：切断空間と相対関手空間の同型、および Kan 値図式の Bousfield–Kan end の Kan 性。
方針：二つの切断模型の普遍性を比較し、left fibration の相対関手空間の Kan 性を移す。
規約：添字圏に特別な形や図式の遷移の fibration 性を要求しない。
使われ方：Kerodon 7.4.1.6、7.5.3.12、7.5.4.6 の極限の Kan 模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：恒等射上の相対関手の族の評価はパラメータの前合成と可換。
方針：uncurry の前合成の自然性を使う。
規約：底の射は恒等写像に固定する。
使われ方：Kerodon 5.3.1.5、7.4.1.6 の切断模型の比較。 -/
lemma relativeSectionsUncurry_comp {K E A B : SSet.{u}} {p : E ⟶ K}
    (f : A ⟶ B) (g : B ⟶ relativeFunctorSpace p (𝟙 K)) :
    relativeFunctorUncurry (f ≫ g) = (K ◁ f) ≫ relativeFunctorUncurry g := by
  unfold relativeFunctorUncurry
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：内部 Hom の引き戻しで定義した切断空間は F1 の相対関手空間と同型である。
方針：両模型の普遍的な族を互いに curry し、評価の一意性で両逆関係を示す。
規約：底に指定する関手は恒等射。
使われ方：Kerodon 5.3.1.5、7.4.1.6 の切断空間の既存模型との接続。 -/
noncomputable def simplicialSectionsRelativeIso {K E : SSet.{u}} (p : E ⟶ K) :
    simplicialSections p ≅ relativeFunctorSpace p (𝟙 K) := by
  let h := relativeFunctorCurry (p := p) (a := 𝟙 K) (simplicialSectionsEvaluation p) (by
    rw [simplicialSectionsEvaluation_projection, Category.comp_id])
  let g := simplicialSectionsLift (p := p)
    (relativeFunctorUncurry (𝟙 (relativeFunctorSpace p (𝟙 K)))) (by
      rw [relativeFunctorUncurry_projection, Category.comp_id])
  have hh : relativeFunctorUncurry h = simplicialSectionsEvaluation p :=
    relativeFunctorUncurry_curry _ _
  have hg : (K ◁ g) ≫ simplicialSectionsEvaluation p =
      relativeFunctorUncurry (𝟙 (relativeFunctorSpace p (𝟙 K))) :=
    simplicialSectionsLift_evaluation _ _
  refine ⟨h, g, ?_, ?_⟩
  · apply simplicialSections_hom_ext
    rw [whiskerLeft_comp, Category.assoc, hg, ← relativeSectionsUncurry_comp,
      Category.comp_id, hh, whiskerLeft_id, Category.id_comp]
  · apply relativeFunctorUncurry_injective p (𝟙 K)
    rw [relativeSectionsUncurry_comp, hh, hg]

/-- 概要：left fibration の切断空間は Kan 複体である。
方針：恒等射上の相対関手空間の Kan 性を切断模型の同型で移す。
規約：底と全空間の quasicategory 性は仮定しない。
使われ方：Kerodon 7.4.1.6、7.5.3.12 の切断による極限の Kan 性。 -/
lemma simplicialSections_kanComplex {K E : SSet.{u}} (p : E ⟶ K) [LeftFibration p] :
    KanComplex (simplicialSections p) :=
  kanComplex_of_iso (simplicialSectionsRelativeIso p).symm

/-- 概要：任意の小圏で添字付けた Kan 値図式の Bousfield–Kan end は Kan 複体である。
方針：weighted nerve の射影の left fibration 性から切断空間の Kan 性を得て同型で移す。
規約：遷移の fibration 性や添字圏の有限性を要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の一般の Kan 図式の homotopy 極限模型。 -/
lemma bousfieldKanHolim_kanComplex {I : Type u} [SmallCategory I] (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (bousfieldKanHolim H) := by
  have := simplicialSections_kanComplex (weightedNerveProjection H)
  exact kanComplex_of_iso (bousfieldKanSectionsIso H).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
