module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SimplicialSections

/-!
概要：直積射影の切断空間は底から係数への内部 Hom である。
方針：切断の第二成分を curry し、逆に評価と第一射影を組にする。
規約：任意の底と係数を許す通常の単体集合の同型。
使われ方：Goerss–Jardine VIII §2、Kerodon §7.5.3（Tag 03AP）。自明作用の切断の模型。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K X : SSet.{u})

/-- 概要：直積射影の切断の第二成分を内部 Hom へ送る。
方針：普遍的な切断を第二射影へ合成して curry する。
規約：底は第一因子 K。
使われ方：Goerss–Jardine VIII §2。定値図式の切断の値。 -/
def productSectionsToHom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (fst K X) ⟶ (ihom K).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (fst K X) ≫ snd K X)

lemma productSectionsToHom_uncurry :
    uncurry (productSectionsToHom K X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (fst K X) ≫ snd K X := uncurry_curry _

/-- 概要：内部 Hom の族を直積射影の切断へ戻す。
方針：第一射影と普遍的な評価を組にし、切断の持ち上げを使う。
規約：K に関してパラメーター付きで構成する。
使われ方：Goerss–Jardine VIII §2。写像空間から切断空間への逆比較。 -/
def homToProductSections : (ihom K).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (fst K X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift (lift (fst K ((ihom K).obj X)) ((ihom.ev K).app X)) (by simp)

lemma homToProductSections_evaluation :
    (K ◁ homToProductSections K X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (fst K X) =
      lift (fst K ((ihom K).obj X)) ((ihom.ev K).app X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：直積射影の切断空間と底からの内部 Hom の標準同型。
方針：切断の一意性、直積の二つの射影、curry の往復則を使う。
規約：同型は Kan 性に依存しない。
使われ方：Goerss–Jardine VIII §2。自明作用の hG の写像空間表示の基礎。 -/
def productSectionsIso : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (fst K X) ≅ (ihom K).obj X where
  hom := productSectionsToHom K X
  inv := homToProductSections K X
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [whiskerLeft_comp, Category.assoc, homToProductSections_evaluation,
      whiskerLeft_id, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · erw [Category.assoc, lift_fst, whiskerLeft_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection]
    · rw [Category.assoc, lift_snd]
      exact productSectionsToHom_uncurry K X
  inv_hom_id := by
    apply uncurry_injective
    rw [uncurry_natural_left, productSectionsToHom_uncurry,
      ← Category.assoc, homToProductSections_evaluation, lift_snd]
    rfl

end

end SerrePositivity.KST.Spectra
