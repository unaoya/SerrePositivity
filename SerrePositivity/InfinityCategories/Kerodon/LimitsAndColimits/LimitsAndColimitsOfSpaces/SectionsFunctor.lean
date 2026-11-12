module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan

/-!
概要：底を保つ写像に関する切断空間の関手性。
方針：普遍的な切断の族を後合成し、切断空間へ持ち上げる。
規約：底は固定し、全空間と写像に Kan 性や fibration 性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の二つの切断模型を比較する界面。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {K E E' E'' : SSet.{u}}

/-- 概要：底を保つ写像は切断空間の写像を誘導する。
方針：普遍的な切断を後合成し、その底の固定条件で持ち上げる。
規約：底への可換条件を厳密な等式で指定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断模型の比較射。 -/
noncomputable def simplicialSectionsMap {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p ≫ f) (by
    rw [Category.assoc, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection])

/-- 概要：切断空間の誘導写像の評価は元の写像の後合成である。
方針：切断空間への持ち上げの評価の式を使う。
規約：底を保つ全空間の任意の写像に適用できる。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較射の可換図式。 -/
lemma simplicialSectionsMap_evaluation {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) :
    (K ◁ simplicialSectionsMap f hf) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：全空間の恒等写像が切断空間に誘導する写像は恒等射である。
方針：普遍的な切断の族で評価し、一意性を使う。
規約：可換条件には恒等射の合成の等式を使う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断関手の恒等則。 -/
lemma simplicialSectionsMap_id (p : E ⟶ K) :
    simplicialSectionsMap (𝟙 E) (Category.id_comp p) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [simplicialSectionsMap_evaluation, Category.comp_id, whiskerLeft_id, Category.id_comp]

/-- 概要：底を保つ写像の合成は切断空間の誘導写像の合成になる。
方針：評価の公式を二度使い、評価の一意性を適用する。
規約：各可換条件の証明の選択には依存しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断関手の合成則。 -/
lemma simplicialSectionsMap_comp {p : E ⟶ K} {q : E' ⟶ K} {r : E'' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) (g : E' ⟶ E'') (hg : g ≫ r = q) :
    simplicialSectionsMap (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      simplicialSectionsMap f hf ≫ simplicialSectionsMap g hg := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [simplicialSectionsMap_evaluation, whiskerLeft_comp, Category.assoc,
    simplicialSectionsMap_evaluation]
  simp only [← Category.assoc]
  rw [simplicialSectionsMap_evaluation]

/-- 概要：固定した底の上の単体集合から切断空間への通常の関手。
方針：底上の写像から切断空間の写像を作り、恒等と合成の式を使う。
規約：通常の over 圏を始域とする。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の係数図式による切断模型の関手性。 -/
noncomputable def simplicialSectionsFunctor (K : SSet.{u}) : Over K ⥤ SSet.{u} where
  obj p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p.hom
  map f := simplicialSectionsMap f.left (Over.w f)
  map_id p := simplicialSectionsMap_id p.hom
  map_comp f g := simplicialSectionsMap_comp f.left (Over.w f) g.left (Over.w g)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
