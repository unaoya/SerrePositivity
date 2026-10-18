module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportPostcomparison

/-!
概要：切断空間と strict transport の end の標準比較は全空間の射について自然である。
方針：under 圏への制限と後合成が可換なことを評価で示し、錐の比較の自然性を使う。
規約：底を保つ実際の射を使い、全空間の同値性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の fiber ごとの比較を切断空間の比較へ移す可換図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I] {E E' : SSet.{u}}

/-- 概要：切断の under 圏への制限は底を保つ全空間の後合成と可換である。
方針：相対関手を展開し、直積の二因子の射を交換して普遍的な切断の評価で比較する。
規約：射影に left fibration 性を要求しない。
使われ方：Kerodon 5.3.1.5、7.4.1.6 の切断空間の通常の極限錐の自然性。 -/
lemma transportSectionsRestriction_post (p : E ⟶ nerve I) (q : E' ⟶ nerve I)
    (f : E ⟶ E') (hf : f ≫ q = p) (i : I) :
    simplicialSectionsMap f hf ≫ transportSectionsRestriction q i =
      transportSectionsRestriction p i ≫ (strictTransportPost p q f hf).app i := by
  apply relativeFunctorUncurry_injective q (nerveMap (Under.forget i))
  rw [relativeFunctorUncurry_parameter, transportSectionsRestriction_evaluation]
  change _ = relativeFunctorUncurry
    (transportSectionsRestriction p i ≫ relativeFunctorPost p q f hf (nerveMap (Under.forget i)))
  rw [relativeFunctorUncurry_post, transportSectionsRestriction_evaluation,
    ← Category.assoc, whisker_exchange, Category.assoc, simplicialSectionsMap_evaluation,
    ← Category.assoc]

/-- 概要：切断から transport の end への比較は底を保つ全空間の射について自然である。
方針：切断が担う通常の錐の成分の自然性に、重み付き錐の比較の自然性を適用する。
規約：標準比較射そのものの厳密な可換性を述べる。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の全空間の比較と end の同値不変性の接続。 -/
lemma strictTransportSectionsComparison_naturality
    (p : E ⟶ nerve I) (q : E' ⟶ nerve I) (f : E ⟶ E') (hf : f ≫ q = p) :
    simplicialSectionsMap f hf ≫ strictTransportSectionsComparison q =
      strictTransportSectionsComparison p ≫
        weightedSectionsMap (bousfieldKanWeight I) (strictTransportPost p q f hf) :=
  weightedConeComparison_naturality (bousfieldKanWeight I)
    (transportSectionsCone p) (transportSectionsCone q) (simplicialSectionsMap f hf)
    (strictTransportPost p q f hf) (transportSectionsRestriction_post p q f hf)

end SerrePositivity.InfinityCategories.HomotopyLimits
