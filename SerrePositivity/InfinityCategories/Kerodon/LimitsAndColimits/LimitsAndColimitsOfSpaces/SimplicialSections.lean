module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionParameter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：単体集合の射の切断空間を内部 Hom の恒等写像上の引き戻しで定義する。
方針：閉構造の随伴と引き戻しの普遍性を組み合わせる。
規約：任意の単体集合の射を扱い、fibration 性や Kan 性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の極限を計算する切断模型。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {K E A : SSet.{u}}

/-- 概要：p の切断空間は内部 Hom の後合成の射の恒等写像上の fiber である。
方針：恒等写像の点を第一射影の curry で表示して引き戻す。
規約：点の模型にはモノイダル単位を使う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の切断の単体集合。 -/
noncomputable def simplicialSections (p : E ⟶ K) : SSet.{u} :=
  pullback ((ihom K).map p) (curry (fst K (𝟙_ SSet.{u})))

/-- 概要：切断空間の普遍的な切断の族。
方針：引き戻しの内部 Hom への射影を uncurry する。
規約：底は第一因子 K、パラメータは切断空間。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の切断の普遍性。 -/
noncomputable def simplicialSectionsEvaluation (p : E ⟶ K) :
    K ⊗ simplicialSections p ⟶ E :=
  uncurry (pullback.fst ((ihom K).map p) (curry (fst K (𝟙_ SSet.{u}))))

/-- 概要：普遍的な切断の族は底への射と合成すると第一射影になる。
方針：引き戻しの可換性を uncurry し、直積の第一射影の自然性を使う。
規約：底への条件は厳密な等式である。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の切断の固定条件。 -/
lemma simplicialSectionsEvaluation_projection (p : E ⟶ K) :
    simplicialSectionsEvaluation p ≫ p = fst K (simplicialSections p) := by
  rw [simplicialSectionsEvaluation, ← uncurry_natural_right, pullback.condition,
    uncurry_natural_left, uncurry_curry, whiskerLeft_fst]

/-- 概要：底を保つ切断の族は切断空間への射へ持ち上がる。
方針：族を curry し、底の固定条件で引き戻しへ持ち上げる。
規約：パラメータは任意の単体集合。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の切断空間の普遍性。 -/
noncomputable def simplicialSectionsLift {p : E ⟶ K} (s : K ⊗ A ⟶ E)
    (hs : s ≫ p = fst K A) : A ⟶ simplicialSections p :=
  pullback.lift (curry s) (toUnit A) (by
    rw [← curry_natural_right, hs, ← curry_natural_left, whiskerLeft_fst])

/-- 概要：切断空間への持ち上げを普遍的な族で評価すると元の族になる。
方針：引き戻しの第一射影の式と curry と uncurry の逆関係を使う。
規約：底の条件の証明の選択には依存しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の普遍性の存在部分。 -/
lemma simplicialSectionsLift_evaluation {p : E ⟶ K} (s : K ⊗ A ⟶ E)
    (hs : s ≫ p = fst K A) :
    (K ◁ simplicialSectionsLift s hs) ≫ simplicialSectionsEvaluation p = s := by
  rw [simplicialSectionsEvaluation, ← uncurry_natural_left, simplicialSectionsLift,
    pullback.lift_fst, uncurry_curry]

/-- 概要：切断空間への二つの射は普遍的な族での評価で一意に決まる。
方針：uncurry の単射性で第一射影を比較し、第二射影は終対象性で比較する。
規約：任意のパラメータからの実際の射を比較する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の普遍性の一意性部分。 -/
lemma simplicialSections_hom_ext {p : E ⟶ K} {f g : A ⟶ simplicialSections p}
    (h : (K ◁ f) ≫ simplicialSectionsEvaluation p =
      (K ◁ g) ≫ simplicialSectionsEvaluation p) : f = g := by
  apply pullback.hom_ext
  · apply (ihom.adjunction K).homEquiv _ _ |>.symm.injective
    exact h
  · exact isTerminalTensorUnit.hom_ext _ _

/-- 概要：切断空間への射と底を保つ切断の族は全単射で対応する。
方針：普遍的な評価と引き戻しへの持ち上げを両逆関係で組み合わせる。
規約：全てのパラメータで同じ切断空間を使う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1） の切断空間の表現性。 -/
noncomputable def simplicialSectionsHomEquiv (p : E ⟶ K) (A : SSet.{u}) :
    (A ⟶ simplicialSections p) ≃ {s : K ⊗ A ⟶ E // s ≫ p = fst K A} where
  toFun f := ⟨(K ◁ f) ≫ simplicialSectionsEvaluation p, by
    rw [Category.assoc, simplicialSectionsEvaluation_projection, whiskerLeft_fst]⟩
  invFun s := simplicialSectionsLift s.val s.property
  left_inv f := by
    apply simplicialSections_hom_ext
    exact simplicialSectionsLift_evaluation _ _
  right_inv s := Subtype.ext (simplicialSectionsLift_evaluation s.val s.property)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
