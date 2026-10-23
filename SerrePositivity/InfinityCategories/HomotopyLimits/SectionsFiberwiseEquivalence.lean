module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsFunctor
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostEquivalence

/-!
概要：任意の quasicategory 上の left fibrations の fiber 同値は切断空間の同値を誘導する。
方針：相対関手空間との同型の自然性を使い、F1 の底上の逆射による後合成同値を移す。
規約：全空間の比較射に fibration 性を要求しない。
使われ方：Kerodon 5.6.0.6、7.4.1.6、HTT 4.2.4.1 の一般の切断比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：切断空間と相対関手空間の同型は底上の後合成と可換。
方針：相対関手の族を展開し、切断の評価の後合成の式で比較する。
規約：底 K と二つの射影の充填性は不要。
使われ方：Kerodon 7.4.1.6、切断空間への相対後合成の同値性の移送。 -/
lemma simplicialSectionsRelativeIso_naturality {K E E' : SSet.{u}}
    (p : E ⟶ K) (q : E' ⟶ K) (f : E ⟶ E') (hf : f ≫ q = p) :
    simplicialSectionsMap f hf ≫ (simplicialSectionsRelativeIso q).hom =
      (simplicialSectionsRelativeIso p).hom ≫ relativeFunctorPost p q f hf (𝟙 K) := by
  apply relativeFunctorUncurry_injective q (𝟙 K)
  rw [relativeFunctorUncurry_post, relativeSectionsUncurry_comp]
  simp only [simplicialSectionsRelativeIso, relativeFunctorUncurry_curry]
  exact simplicialSectionsMap_evaluation f hf

/-- 概要：任意の quasicategory 上の fiber ごとの同値は切断空間のホモトピー同値を与える。
方針：fiber 同値から底上の前合成同値を得て相対後合成へ移し、標準同型を消去する。
規約：底の形状と比較射 f の充填性に追加の条件を要求しない。
使われ方：Kerodon 5.6.0.6、7.4.1.6、HTT 4.2.4.1 の coherent な錐の一般比較。 -/
lemma simplicialSectionsMap_homotopyEquivalence_of_fibers
    {K E E' : SSet.{u}} [Quasicategory K]
    (p : E ⟶ K) (q : E' ⟶ K) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsSimplicialHomotopyEquivalence (simplicialSectionsMap f hf) := by
  have := simplicialSections_kanComplex p
  have := simplicialSections_kanComplex q
  have he := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q f hf (isPrecompositionEquivalence_of_leftFibration_fibers p q f hf h) (𝟙 K)
  have hp := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso p)).isQCatEquivalence
  have hq := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso q)).isQCatEquivalence
  apply IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply hq.cancel_right
  change IsQCatEquivalence
    (simplicialSectionsMap f hf ≫ (simplicialSectionsRelativeIso q).hom)
  rw [simplicialSectionsRelativeIso_naturality]
  exact hp.comp he

end SerrePositivity.InfinityCategories.HomotopyLimits
